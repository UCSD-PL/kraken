Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
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

Inductive COMPT : Set := Tab | Screen | UserInput.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Tab       => mk_compd "Tab"       "test/quark/tab.py"        [] (mk_vdesc [str_d])
  | Screen    => mk_compd "Screen"    "test/quark/screen.py"     [] (mk_vdesc [])
  | UserInput => mk_compd "UserInput" "test/quark/user-input.py" [] (mk_vdesc [])
  end.

Definition default_domain := str_of_string "google.com".

Definition IMSG : msg PAYD := @Build_msg _ PAYD Quit tt.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IMSG IENVD :=
  [ fun s => Spawn _ _ COMPS _ _ IENVD Tab       (default_domain, tt) None (Logic.eq_refl _)
  ; fun s => Spawn _ _ COMPS _ _ IENVD Screen    tt                   None (Logic.eq_refl _)
  ; fun s => Spawn _ _ COMPS _ _ IENVD UserInput tt                   None (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  (fun m cfd =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with

    | Input => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD m d) envd (
         let (input, _) := pl in fun st0 =>
         if fd_eq cfd (shvec_ith (n := projT1 KSTD) _
                                 (projT2 KSTD) (kst _ _ _ _ st0) userinput)
         then
           [ fun s => Send PAYD COMPT COMPS KSTD _ envd
                           (StVar _ KSTD m _ curtab) Input
                           (SLit _ _ m _  input, tt) ]
         else
           []
       )

    | Display => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD m d) envd (
         let (url, _) := pl in fun st0 =>
         if fd_eq cfd (shvec_ith (n := projT1 KSTD) _
                                 (projT2 KSTD) (kst _ _ _ _ st0) curtab)
         then
           [ fun s => Send PAYD COMPT COMPS KSTD _ envd
                           (StVar _ KSTD m _ screen) Display
                           (SLit _ _ m _ url, tt) ]
         else
           []
       )

    | Quit => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD m d) envd (
         let _ := pl in fun st0 =>
         if fd_eq
              cfd
              (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD) (kst _ _ _ _ st0) userinput)
         then
           [ fun s => Send PAYD COMPT COMPS KSTD _ envd
                           (StVar _ KSTD m _ curtab) Quit tt
           ; fun s => Send PAYD COMPT COMPS KSTD _ envd
                           (StVar _ KSTD m _ screen) Quit tt
           ]
         else
           []
       )

    | Some (Some (Some bad)) => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD COMPT COMPTDEC COMPS IMSG INIT HANDLERS).
