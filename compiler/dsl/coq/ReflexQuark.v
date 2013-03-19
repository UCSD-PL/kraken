Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.

Open Scope string_scope.

Definition NB_MSG : nat := 3.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ ("Input",   [str_d])
  ; ("Display", [str_d])
  ; ("Quit",    [ ])
  ].

Definition KSTD : vdesc := mk_vdesc
  [ fd_d (* curtab *)
  ; fd_d (* screen *)
  ].

Definition IENVD : vdesc := mk_vdesc [].

Inductive COMPT : Type := Tab | Screen | UserInput.

Definition COMPS (t : COMPT) : comp :=
  match t with
  | Tab       => mk_comp "Tab"       "test/quark/tab.py"        []
  | Screen    => mk_comp "Screen"    "test/quark/screen.py"     []
  | UserInput => mk_comp "UserInput" "test/quark/user-input.py" []
  end.

Definition INIT : init_prog PAYD COMPT KSTD IENVD :=
  [ fun s => Spawn _ _ _ _ Tab
  ; fun s => Spawn _ _ _ _ Screen
  ].

Definition HANDLERS : handlers PAYD COMPT KSTD :=
  (fun m =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with

(* Input *)
    | None => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (fun cfd s =>
         let (input, _) := pl in
         (fun st0 =>
                                                 (* should be curtab *)
            [ fun s => Send PAYD COMPT KSTD envd (CFd _) None (SLit _ input, tt)
            ]
         )
       )

(* Display *)
    | Some None => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (fun cfd s =>
         let (url, _) := pl in
         (fun st0 =>
            [ fun s => Send PAYD COMPT KSTD envd (CFd _) (Some None) (SLit _ url, tt)
            ]
         )
       )

(* Quit *)
    | Some (Some None) => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (fun cfd s =>
         let _ := pl in
         (fun st0 =>
           []
         )
       )

    | Some (Some (Some bad)) => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD COMPT COMPS INIT HANDLERS).
