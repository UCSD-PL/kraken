open Common
open Spec

let fmt_concat sep fmt l =
  l |> List.map fmt
    |> String.concat sep

(* generate unique id # for each message tag *)
(* start at 1 so BadTag can always have id 0 *)
let gen_tag_map s =
  let tags = List.map tag s.msg_decl in
  List.combine tags (range 1 (List.length tags + 1))

(*
 * COQ TURN MODULE
 *)

let decl md =
  let args =
    List.fold_right
      (function Num -> mkstr "num -> %s"
              | Str -> mkstr "str -> %s")
      md.payload
      "msg"
  in
  mkstr "| %s : %s" md.tag args
;;

let args_str md =
  md.payload
    |> List.mapi (fun i _ -> mkstr "p%d" i)
    |> String.concat " "
;;

let recv_trace tag_map md =
  let hdr =
    mkstr "    | %s %s =>" md.tag (args_str md)
  in
  let pay =
    md.payload
      |> List.mapi (fun i ->
          function Num -> mkstr "      RecvNum c p%d ++" i
                 | Str -> mkstr "      RecvStr c p%d ++" i)
      |> List.rev
      |> String.concat "\n"
  in
  let tag =
    mkstr "      RecvNum c (Num \"%03d\")"
      (List.assoc md.tag tag_map)
  in
  mkstr "%s\n%s\n%s"
    hdr pay tag
;;

(* WARNING copy/paste of recv_trace *)
let send_trace tag_map md =
  let hdr =
    mkstr "    | %s %s =>" md.tag (args_str md)
  in
  let pay =
    md.payload
      |> List.mapi (fun i ->
          function Num -> mkstr "      SendNum c p%d ++" i
                 | Str -> mkstr "      SendStr c p%d ++" i)
      |> List.rev
      |> String.concat "\n"
  in
  let tag =
    mkstr "      SendNum c (Num \"%03d\")"
      (List.assoc md.tag tag_map)
  in
  mkstr "%s\n%s\n%s"
    hdr pay tag
;;

let recv tag_map md =
  let hdr =
    mkstr "      | Num \"%03d\" => (* %s *)"
      (List.assoc md.tag tag_map) md.tag
  in
  let pay =
    let recv_typ = function
      | Num -> "recvNum"
      | Str -> "recvStr"
    in
    let recv_typ_trace = function
      | Num -> "RecvNum"
      | Str -> "RecvStr"
    in
    let aux (acc, tr, i) t =
      ((mkstr "        p%d <- %s c\n" i (recv_typ t) ^
        mkstr "          (tr ~~~ %s);" tr) :: acc
      , mkstr "%s c p%d ++ %s" (recv_typ_trace t) i tr
      , i + 1
      )
    in
    let tr =
      mkstr "RecvNum c (Num \"%03d\") ++ tr"
        (List.assoc md.tag tag_map)
    in
    md.payload
      |> List.fold_left aux ([], tr, 0)
      |> fun (x, _, _) -> x
      |> List.rev
      |> String.concat "\n"
  in
  let ret =
    mkstr "        {{ Return (%s %s) }}" md.tag (args_str md)
  in
  mkstr "%s\n%s\n%s"
    hdr pay ret
;;

(* WARNING copy/paste of recv *)
let send tag_map md =
  let hdr =
    mkstr "      | %s %s =>\n" md.tag (args_str md) ^
    mkstr "        sendNum c (Num \"%03d\")\n" (List.assoc md.tag tag_map) ^
    mkstr "          tr;;"
  in
  let pay =
    let send_typ = function
      | Num -> "sendNum"
      | Str -> "sendStr"
    in
    let send_typ_trace = function
      | Num -> "SendNum"
      | Str -> "SendStr"
    in
    let aux (acc, tr, i) t =
      ((mkstr "        %s c p%d\n" (send_typ t) i ^
        mkstr "          (tr ~~~ %s);;" tr) :: acc
      , mkstr "%s c p%d ++ %s" (send_typ_trace t) i tr
      , i + 1
      )
    in
    let tr =
      mkstr "SendNum c (Num \"%03d\") ++ tr"
        (List.assoc md.tag tag_map)
    in
    md.payload
      |> List.fold_left aux ([], tr, 0)
      |> fun (x, _, _) -> x
      |> List.rev
      |> String.concat "\n"
  in
  let ret =
    "        {{ Return tt }}"
  in
  mkstr "%s\n%s\n%s"
    hdr pay ret
;;

let proto hand =
  let pat =
    let p = snd hand.trigger in
    mkstr "  | %s %s =>"
      p.tag (String.concat " " p.payload)
  in
  let body =
    let rec sends = function
      | Send (_, m) -> [m]
      | Seq (p1, p2) -> sends p1 @ sends p2
    in
    let rec expr_str = function
      | Var id -> id
      | NumLit n -> mkstr "%d" n
      | StrLit s ->
          s |> explode
            |> List.map (mkstr "\"%c\" :: ")
            |> String.concat ""
            |> mkstr "%snil"
    in
    let aux m =
      mkstr "    %s %s ::" m.tag
        (m.payload
          |> List.map expr_str
          |> String.concat ") ("
          |> mkstr "(%s)")
    in
    hand.respond
      |> sends
      |> List.map aux
      |> String.concat "\n"
      |> mkstr "%s\n    nil"
  in
  mkstr "%s\n%s" pat body
;;

(* turn template has string holes for
 *  1. declaring msg
 *  2. RecvMsg cases
 *  3. SendMsg cases
 *  4. recvMsg cases
 *  5. sendMsg cases
 *  6. protocol cases
 *)
let turn_template = format_of_string "
Require Import List.
Require Import Ascii.
Require Import Ynot.
Require Import KrakenBase.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Inductive msg : Set :=
%s
(* special case for errors *)
| BadTag : num -> msg.

Definition RecvMsg (c : chan) (m : msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      RecvNum c p0
  end.

Definition SendMsg (c : chan) (m : msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      SendNum c (Num \"000\")
  end.

Definition recvMsg :
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (m : msg) => tr ~~ traced (RecvMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    tag <- recvNum c
      tr;
    match tag with
%s
      (* special case for errors *)
      | m =>
        {{ Return (BadTag m) }}
    end
  );
  sep fail auto;
    repeat rewrite app_ass; simpl;
    sep fail auto.
Qed.

Definition sendMsg :
  forall (c : chan) (m : msg) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    match m with
%s
      (* special case for errors *)
      | BadTag _ =>
        sendNum c (Num \"000\")
          tr;;
        {{ Return tt }}
    end
  );
  sep fail auto;
    repeat rewrite app_ass; simpl;
    sep fail auto.
Qed.

Fixpoint SendMsgs (c : chan) (ms : list msg) : Trace :=
  match ms with
    | m :: ms' => SendMsgs c ms' ++ SendMsg c m
    | nil => nil
  end.

Definition sendMsgs :
  forall (c : chan) (ms : list msg) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendMsgs c ms ++ tr) * bound c).
Proof.
  intros; refine (
    Fix2
      (fun ms tr => tr ~~ traced tr * bound c)
      (fun ms tr (_ : unit) => tr ~~ traced (SendMsgs c ms ++ tr) * bound c)
      (fun self ms tr =>
        match ms with
          | m :: ms' =>
            sendMsg c m
              tr;;
            self ms'
              (tr ~~~ SendMsg c m ++ tr);;
            {{ Return tt }}
          | nil =>
            {{ Return tt }}
        end)
      ms tr
  );
  sep fail auto;
    repeat rewrite app_ass; simpl;
    sep fail auto.
Qed.

Definition protocol (m : msg) : list msg :=
  match m with
%s
  | _ =>
    nil
  end.

Definition turn :
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (req : msg) => tr ~~ traced (SendMsgs c (protocol req) ++ RecvMsg c req ++ tr) * bound c).
Proof.
  intros; refine (
    req <- recvMsg c
      tr;
    sendMsgs c (protocol req)
      (tr ~~~ RecvMsg c req ++ tr);;
    {{ Return req }}
  );
  sep fail auto.
Qed.
"

let turn s =
  let m = gen_tag_map s in
  mkstr turn_template
    (s.msg_decl |> fmt_concat "\n" decl)
    (s.msg_decl |> fmt_concat "\n" (recv_trace m))
    (s.msg_decl |> fmt_concat "\n" (send_trace m))
    (s.msg_decl |> fmt_concat "\n" (recv m))
    (s.msg_decl |> fmt_concat "\n" (send m))
    (s.protocol |> fmt_concat "\n" proto)

(*
 * PYTHON MESSAGING LIBRARY
 *)

let recv tag_map md =
  let args =
    md.payload
      |> List.map (function Num -> "recvNum(c)"
                          | Str -> "recvStr(c)")
      |> String.concat ", "
  in
  mkstr "    %2d : lambda x : Msg('%s', [%s]),"
    (List.assoc md.tag tag_map) md.tag args
;;

(* WARNING copy/paste of recv *)
let send tag_map md =
  let args =
    md.payload
      |> List.mapi (fun i ->
          function Num -> mkstr "sendNum(c, m.params[%d])" i
                 | Str -> mkstr "sendStr(c, m.params[%d])" i)
      |> String.concat ", "
  in
  mkstr "    '%s' : lambda x : [sendNum(c, %d), %s],"
    md.tag (List.assoc md.tag tag_map) args
;;

(* py lib template has string holes for
 *  1. recvMsg cases
 *  2. sendMsg cases
 *)
let py_lib_template = format_of_string "
import socket, struct

def recvNum(c):
  s = c.recv(1)
  n = struct.unpack('>B', s)[0]
  return n

def recvStr(c):
  n = recvNum(c)
  s = c.recv(n)
  return s

def sendNum(c, n):
  s = struct.pack('>B', n)
  c.send(s)

def sendStr(c, s):
  sendNum(c, len(s))
  c.send(s)

class Msg:
  def __init__(self, tag, params):
    self.tag = tag
    self.params = params

def recvMsg(c):
  tag = recvNum(c)
  msg = {
%s
  }[tag](0)
  return msg

def sendMsg(c, m):
  {
%s
  }[m.tag](0)
"

let py_lib s =
  let m = gen_tag_map s in
  mkstr py_lib_template
    (s.msg_decl |> fmt_concat "\n" (recv m))
    (s.msg_decl |> fmt_concat "\n" (send m))

(*
 * C MESSAGING LIBRARY
 *)

let c_lib s =
  ""

(*
 * ML MESSAGING LIBRARY
 *)

let ml_lib s =
  ""
