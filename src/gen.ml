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
              | Str -> mkstr "str -> %s"
              | Fdesc -> mkstr "fdesc -> %s")
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
          function Num   -> mkstr "      RecvNum c p%d ++" i
                 | Str   -> mkstr "      RecvStr c p%d ++" i
                 | Fdesc -> mkstr "      RecvFD  c p%d ::" i)
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
          function Num   -> mkstr "      SendNum c p%d ++" i
                 | Str   -> mkstr "      SendStr c p%d ++" i 
                 | Fdesc -> mkstr "      SendFD  c p%d ::" i)
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
    let typ_handlers = function
      | Num -> "recv_num", "RecvNum", "++"
      | Str -> "recv_str", "RecvStr", "++"
      | Fdesc -> "recv_fd", "RecvFD", "::"
    in
    let aux (i, acc, tr) t =
      let recvF, recvT, conn = typ_handlers t in
      ( i + 1
      , mkstr "%8sp%d <- %s c\n%10s(tr ~~~ %s);" "" i recvF "" tr :: acc
      , mkstr "%s c p%d %s %s" recvT i conn tr
      )
    in
    let tr =
      mkstr "RecvNum c (Num \"%03d\") ++ tr"
        (List.assoc md.tag tag_map)
    in
    md.payload
      |> List.fold_left aux (0, [], tr)
      |> fun (_, x, _) -> x
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
    mkstr "        send_num c (Num \"%03d\")\n" (List.assoc md.tag tag_map) ^
    mkstr "          tr;;"
  in
  let pay =
    let typ_handlers = function
      | Num -> "send_num", "SendNum", "++"
      | Str -> "send_str", "SendStr", "++"
      | Fdesc -> "send_fd", "SendFD", "::"
    in
    let aux (i, acc, tr) t =
      let sendF, sendT, conn = typ_handlers t in
      ( i + 1
      , mkstr "%8s%s c p%d\n%10s(tr ~~~ %s);;" "" sendF i "" tr :: acc
      , mkstr "%s c p%d %s %s" sendT i conn tr
      )
    in
    let tr =
      mkstr "SendNum c (Num \"%03d\") ++ tr"
        (List.assoc md.tag tag_map)
    in
    md.payload
      |> List.fold_left aux (0, [], tr)
      |> fun (_, x, _) -> x
      |> List.rev
      |> String.concat "\n"
  in
  let ret =
    "        {{ Return tt }}"
  in
  mkstr "%s\n%s\n%s"
    hdr pay ret
;;

let handler_vars hand =
  let trigger_vars t =
    "c" :: (snd t).payload
  in
  let expr_vars = function
    | Var id -> [id]
    | _ -> []
  in
  let cmd_vars = function
    | Send (_, m) ->
        m.payload
          |> List.map expr_vars
          |> List.flatten
    | Call (var, _, arg) ->
        var :: expr_vars arg
  in
  let rec prog_vars = function
    | Nop -> []
    | Seq (c, p) -> cmd_vars c @ prog_vars p
  in
  uniq ((trigger_vars hand.trigger) @ (prog_vars hand.respond))
;;

let valid_exchange hand =
  let hdr =
    let pat = snd hand.trigger in
    mkstr "| VE_%s :\n  forall %s,\n  ValidExchange ("
      pat.tag (hand |> handler_vars |> String.concat " ")
  in
  let body =
    let expr_str_aux = function
      | Var id -> id
      | NumLit n -> mkstr "%d" n
      | StrLit s ->
          s |> explode
            |> List.map (mkstr "\"%c\" :: ")
            |> String.concat ""
            |> mkstr "%snil"
    in
    let expr_str e =
      mkstr "(%s)" (expr_str_aux e)
    in
    let msg_str m =
      mkstr "(%s %s)" m.tag
        (m.payload
          |> List.map expr_str
          |> String.concat " ")
    in
    let cmd_trace = function
      | Send (c, m) ->
          mkstr "    SendMsg c %s ++" (msg_str m)
      | Call (var, f, arg) ->
          mkstr "    Call %s %s %s ::" (expr_str (StrLit f)) (expr_str arg) var
    in
    let rec loop acc = function
      | Nop -> acc
      | Seq (cmd, prog) ->
          loop (cmd_trace cmd :: acc) prog
    in
    hand.respond
      |> loop []
      |> String.concat "\n"
  in
  let ftr =
    let msg_str m =
      mkstr "(%s %s)" m.tag
        (m.payload
          |> String.concat " ")
    in
    mkstr "RecvMsg c %s)"
      (msg_str (snd hand.trigger))
  in
  mkstr "%s\n%s\n%s"
    hdr body ftr
;;

let exchange hand =
  let hdr =
    let mp = snd hand.trigger in
    mkstr "      | %s %s =>"
      mp.tag (String.concat " " mp.payload)
  in
  let body =
    let expr_str_aux = function
      | Var id -> id
      | NumLit n -> mkstr "%d" n
      | StrLit s ->
          s |> explode
            |> List.map (mkstr "\"%c\" :: ")
            |> String.concat ""
            |> mkstr "%snil"
    in
    let expr_str e =
      mkstr "(%s)" (expr_str_aux e)
    in
    let handle_cmd (acc, tr) = function
      | Call (id, f, arg) ->
          (mkstr "      %s <- call %s %s\n" id (expr_str (StrLit f)) (expr_str arg) ^
           mkstr "        (tr ~~~ %s ++ tr) <@>\n" tr ^
           mkstr "        bound c;") :: acc,
          mkstr "Call %s %s %s :: %s" (expr_str (StrLit f)) (expr_str arg) id tr
      | Send (_, m) ->
          (mkstr "      sendMsg c (%s %s)\n" m.tag (m.payload |> List.map expr_str |> String.concat " ") ^
           mkstr "        (tr ~~~ %s ++ tr);;" tr) :: acc,
          mkstr "SendMsg c (%s %s) ++ %s" m.tag (m.payload |> List.map expr_str |> String.concat " ") tr
    in
    let rec loop (acc, tr) = function
      | Nop -> 
          ((mkstr "      {{ Return (inhabits (%s)) }}" tr) :: acc)
            |> List.rev
            |> String.concat "\n"
      | Seq (c, p) ->
          loop (handle_cmd (acc, tr) c) p
    in
    let tr =
      let mp = snd hand.trigger in
      mkstr "RecvMsg c (%s %s)"
        mp.tag (String.concat " " mp.payload)
    in
    loop ([], tr) hand.respond
  in
  mkstr "%s\n%s"
    hdr body
;;

(* turn template has string holes for
 *  1. declaring msg
 *  2. RecvMsg cases
 *  3. SendMsg cases
 *  4. recvMsg cases
 *  5. sendMsg cases
 *  6. ValidExchange cases
 *  7. exchange cases
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

(* prevent sep tactic from unfolding *)
Global Opaque RecvMsg.

Definition SendMsg (c : chan) (m : msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      SendNum c (Num \"000\")
  end.

(* prevent sep tactic from unfolding *)
Global Opaque SendMsg.

Definition recvMsg :
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (m : msg) => tr ~~ traced (RecvMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    tag <- recv_num c
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
        send_num c (Num \"000\")
          tr;;
        {{ Return tt }}
    end
  );
  sep fail auto;
  repeat rewrite app_ass; simpl;
  sep fail auto.
Qed.

Inductive ValidExchange : Trace -> Prop :=
%s
(* special case for errors *)
| VE_BadTag :
  forall c tag,
  ValidExchange (
    RecvMsg c (BadTag tag)).

Definition exchange :
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (tr' : [Trace]) => tr' ~~ tr ~~ traced (tr' ++ tr) * [ValidExchange tr'] * bound c).
Proof.
  intros; refine (
    req <- recvMsg c
      tr;
    match req with
%s
      (* special case for errors *)
      | BadTag tag =>
        {{ Return (tr ~~~ RecvMsg c (BadTag tag)) }}
    end

  );
  sep fail auto;
  apply himp_pure'; constructor; auto.
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
    (s.protocol |> fmt_concat "\n" valid_exchange)
    (s.protocol |> fmt_concat "\n" exchange)

(*
 * PYTHON MESSAGING LIBRARY
 *)

let recv tag_map md =
  let args =
    md.payload
      |> List.map (function Num -> "recvNum()"
                          | Str -> "recvStr()"
                          | Fdesc -> "recvFD()")

      |> String.concat ", "
  in
  mkstr "    %2d : lambda x : ['%s', %s],"
    (List.assoc md.tag tag_map) md.tag args
;;

(* WARNING copy/paste of recv *)
let send tag_map md =
  let args =
    md.payload
      |> List.mapi (fun i ->
          function Num -> mkstr "sendNum(m[%d])" (i + 1)
                 | Str -> mkstr "sendStr(m[%d])" (i + 1)
                 | Fdesc -> mkstr "sendFD(m[%d])" (i + 1))
      |> String.concat ", "
  in
  mkstr "    '%s' : lambda x : [sendNum(%d), %s],"
    md.tag (List.assoc md.tag tag_map) args
;;

(* py lib template has string holes for
 *  1. recvMsg cases
 *  2. sendMsg cases
 *)
let py_lib_template = format_of_string "
import socket, struct, sys

KCHAN = None

def init():
  global KCHAN
  fd = int(sys.argv[1])
  KCHAN = socket.fromfd(fd, socket.AF_UNIX, socket.SOCK_STREAM)

def recvNum():
  s = KCHAN.recv(1)
  n = struct.unpack('>B', s)[0]
  return n

def recvStr():
  n = recvNum()
  s = KCHAN.recv(n)
  return s

def sendNum(n):
  s = struct.pack('>B', n)
  KCHAN.send(s)

def sendStr(s):
  sendNum(len(s))
  KCHAN.send(s)

def recvMsg():
  tag = recvNum()
  return {
%s
  }[tag](0)

def sendMsg(*m):
  tag = m[0]
  {
%s
  }[tag](0)
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
