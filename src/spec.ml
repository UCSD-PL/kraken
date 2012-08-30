open Common

type id =
  string

type chan =
  string

type typ =
  | Num
  | Str

type expr =
  | NLit of int
  | SLit of string
  | Var  of id

type 'a msg =
  { tag : string
  ; payload : 'a list
  }

let msg t p =
  { tag = t
  ; payload = p
  }

let tag m =
  m.tag

type msg_pat = id msg
type msg_decl = typ msg
type msg_expr = expr msg

type prog =
  | Send of chan * msg_expr
  | Seq of prog * prog

type handler =
  { trigger : chan * msg_pat
  ; respond : prog
  }

let handler t r =
  { trigger = t
  ; respond = r
  }

type spec =
  { msg_decl : msg_decl list
  ; protocol : handler list
  }

let spec m p =
  { msg_decl = m
  ; protocol = p
  }

(* sanity checks *)

let ckspec s =
  (* msg tags start with uppercase *)
  (* msg tags uniq *)
  (* BadTag not in msg tags *)
  ()

(* coq gen *)

let msg_decl_coq mds =
  let fmt md =
    let args =
      let aux arg acc =
        match arg with
        | Num, _ -> "num -> " ^ acc
        | Str, _ -> "str -> " ^ acc
      in
      List.fold_right aux md.payload "msg"
    in
    mkstr "| %s : %s" md.tag args
  in
  mds
    |> List.map fmt
    |> String.concat "\n"
    |> mkstr "
Inductive msg : Set :=
%s
| BadTag : N -> msg.
"

let recv_msg_spec_coq tag_map mds =
  let fmt md =
    let hdr =
      mkstr "    | %s %s =>" md.tag
        (md.payload
          |> List.map snd
          |> String.concat " ")
    in
    let recv_pay =
      let aux = function
        | Num, p -> mkstr "      RecvNum c %s ++" p
        | Str, p -> mkstr "      RecvStr c %s ++" p
      in
      md.payload
        |> List.rev
        |> List.map aux
        |> String.concat "\n"
    in
    let recv_tag =
      mkstr "      RecvNum c %d"
        (List.assoc md.tag tag_map)
    in
    mkstr "%s\n%s\n%s"
      hdr recv_pay recv_tag
  in
  mds
    |> List.map fmt
    |> String.concat "\n"
    |> mkstr "
Definition RecvMsg (c: chan) (m: msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      RecvNum c p0
  end.
"

(* WARNING : copy/paste of recv_msg_spec_coq *)
let send_msg_spec_coq tag_map mds =
  let fmt md =
    let hdr =
      mkstr "    | %s %s =>" md.tag
        (md.payload
          |> List.map snd
          |> String.concat " ")
    in
    let recv_pay =
      let aux = function
        | Num, p -> mkstr "      SendNum c %s ++" p
        | Str, p -> mkstr "      SendStr c %s ++" p
      in
      md.payload
        |> List.rev
        |> List.map aux
        |> String.concat "\n"
    in
    let recv_tag =
      mkstr "      SendNum c %d"
        (List.assoc md.tag tag_map)
    in
    mkstr "%s\n%s\n%s"
      hdr recv_pay recv_tag
  in
  mds
    |> List.map fmt
    |> String.concat "\n"
    |> mkstr "
Definition SendMsg (c: chan) (m: msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      SendNum c 0
  end.
"

let recv_msg_coq tag_map mds =
  let fmt md =
    let hdr =
        mkstr "      | %d => (* %s *)"
          (List.assoc md.tag tag_map) md.tag
    in
    let recv_pay =
      let recv_typ = function
        | Num -> "recvNum"
        | Str -> "recvStr"
      in
      let recv_typ_trace = function
        | Num -> "RecvNum"
        | Str -> "RecvStr"
      in
      let aux (acc, tr) (t, p) =
        ( (mkstr "        %s <- %s c\n" p (recv_typ t) ^
           mkstr "          (tr ~~~ %s);" tr) :: acc
        , mkstr "%s c %s ++ %s" (recv_typ_trace t) p tr
        )
      in
      let tr =
        mkstr "RecvNum c %d ++ tr"
          (List.assoc md.tag tag_map)
      in
       md.payload
        |> List.fold_left aux ([], tr)
        |> fst
        |> List.rev
        |> String.concat "\n"
    in
    let ret =
      mkstr "        {{ Return (%s %s) }}" md.tag
        (md.payload
          |> List.map snd
          |> String.concat " ")
    in
    mkstr "%s\n%s\n%s"
      hdr recv_pay ret
  in
  mds
    |> List.map fmt
    |> String.concat "\n"
    |> mkstr "
Definition recvMsg:
  forall (c: chan) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (m: msg) => tr ~~ traced (RecvMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    tag <- recvNum c
      tr;
    match tag with
%s
      (* special case for errors *)
      | m =>
        {{ Return (BadTag m) }}
    end%%N
  );
  sep fail auto.
Qed.
"

(* WARNING : partial copy/paste of recv_msg_coq *)
let send_msg_coq tag_map mds =
  let fmt md =
    let hdr =
      mkstr "      | %s %s =>\n" md.tag
        (md.payload
          |> List.map snd
          |> String.concat " ") ^
      mkstr "        sendNum c %d\n"
        (List.assoc md.tag tag_map) ^
      mkstr "          tr;;"
    in
    let send_pay =
      let send_typ = function
        | Num -> "sendNum"
        | Str -> "sendStr"
      in
      let send_typ_trace = function
        | Num -> "SendNum"
        | Str -> "SendStr"
      in
      let aux (acc, tr) (t, p) =
        ( (mkstr "        %s c %s\n" (send_typ t) p ^
           mkstr "          (tr ~~~ %s);;" tr) :: acc
        , mkstr "%s c %s ++ %s" (send_typ_trace t) p tr
        )
      in
      let tr =
        mkstr "SendNum c %d ++ tr"
          (List.assoc md.tag tag_map)
      in
       md.payload
        |> List.fold_left aux ([], tr)
        |> fst
        |> List.rev
        |> String.concat "\n"
    in
    let ret =
      "        {{ Return tt }}"
    in
    mkstr "%s\n%s\n%s"
      hdr send_pay ret
  in
  mds
    |> List.map fmt
    |> String.concat "\n"
    |> mkstr "
Definition sendMsg:
  forall (c: chan) (m: msg) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_: unit) => tr ~~ traced (SendMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    match m with
%s
      (* special case for errors *)
      | BadTag _ =>
        sendNum c 0
          tr;;
        {{ Return tt }}
    end
  );
  sep fail auto.
Qed.
"

let spec_coq s =
  (* generate id number for each message tag *)
  (* start at 1 so BadTag can always have id 0 *)
  let tag_map =
    let tags = List.map tag s.msg_decl in
    let ids = range 1 (List.length tags + 1) in
    List.combine tags ids
  in
  (* name each param in a msg_decl *)
  let name_params md =
    let nms =
      List.map (mkstr "p%d")
        (range 0 (List.length md.payload))
    in
    msg md.tag (List.combine md.payload nms)
  in
  let mds =
    List.map name_params s.msg_decl
  in
  mkstr "%s%s%s%s%s"
    (msg_decl_coq mds)
    (recv_msg_spec_coq tag_map mds)
    (send_msg_spec_coq tag_map mds)
    (recv_msg_coq tag_map mds)
    (send_msg_coq tag_map mds)

(* support lex/parse error reporting *)
let line =
  ref 1
