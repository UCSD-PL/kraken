Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexHVec.
Require Import ReflexVec.

Open Scope string_scope.

Definition NB_MSG : nat := 3.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ ("Input",   [str_d])
  ; ("Display", [str_d])
  ; ("Quit",    [ ])
  ].

Notation Input   := (None) (only parsing).
Notation Display := (Some None) (only parsing).
Notation Quit    := (Some (Some None)) (only parsing).

Definition KSTD : vdesc := mk_vdesc
  [ fd_d (* curtab *)
  ; fd_d (* screen *)
  ; fd_d (* user-input *)
  ].

Notation curtab    := (None) (only parsing).
Notation screen    := (Some None) (only parsing).
Notation userinput := (Some (Some None)) (only parsing).

Definition IENVD : vdesc := mk_vdesc
  [ fd_d (* curtab *)
  ; fd_d (* screen *)
  ; fd_d (* userinput *)
  ].

Notation v_t := (None) (only parsing).
Notation v_s := (Some None) (only parsing).
Notation v_u := (Some (Some None)) (only parsing).

Inductive COMPT : Type := Tab | Screen | UserInput.

Definition COMPS (t : COMPT) : comp :=
  match t with
  | Tab       => mk_comp "Tab"       "test/quark/tab.py"        []
  | Screen    => mk_comp "Screen"    "test/quark/screen.py"     []
  | UserInput => mk_comp "UserInput" "test/quark/user-input.py" []
  end.

Definition INIT : init_prog PAYD COMPT KSTD IENVD :=
  [ fun s => Spawn _ _ _ IENVD Tab       v_t (Logic.eq_refl _)
  ; fun s => Spawn _ _ _ IENVD Screen    v_s (Logic.eq_refl _)
  ; fun s => Spawn _ _ _ IENVD UserInput v_u (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT KSTD :=
  (fun m cfd =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with

    | Input => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
         let (input, _) := pl in fun st0 =>
         if fd_eq cfd (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD) (kst _ _ st0) userinput)
         then
           [ fun s => Send PAYD COMPT KSTD envd (StVar KSTD _ curtab) Input (SLit _ _ input, tt) ]
         else
           []
       )

    | Display => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
         let (url, _) := pl in fun st0 =>
         if fd_eq cfd (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD) (kst _ _ st0) curtab)
         then
           [ fun s => Send PAYD COMPT KSTD envd (StVar KSTD _ screen) Display (SLit _ _ url, tt) ]
         else
           []
       )

    | Quit => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
         let _ := pl in fun st0 =>
         if fd_eq cfd (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD) (kst _ _ st0) userinput)
         then
           [ fun s => Send PAYD COMPT KSTD envd (StVar KSTD _ curtab) Quit tt
           ; fun s => Send PAYD COMPT KSTD envd (StVar KSTD _ screen) Quit tt
           ]
         else
           []
       )

    | Some (Some (Some bad)) => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD COMPT COMPS INIT HANDLERS).
