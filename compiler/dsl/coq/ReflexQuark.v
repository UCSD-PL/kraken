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

Inductive COMPT : Type := Tab | Screen | UserInput.

Definition COMPS (t : COMPT) : comp :=
  match t with
  | Tab       => mk_comp "Tab"       "test/quark/tab.py"        []
  | Screen    => mk_comp "Screen"    "test/quark/screen.py"     []
  | UserInput => mk_comp "UserInput" "test/quark/user-input.py" []
  end.

Definition NB_CFGD := 1.

Definition CFGD := mk_vvdesc [("",[])].

Definition INIT : init_prog PAYD COMPT KSTD CFGD (init_msg PAYD) IENVD :=
  [ fun s => Spawn _ _ _ CFGD _ IENVD Tab       None tt v_t (Logic.eq_refl _)
  ; fun s => Spawn _ _ _ CFGD _ IENVD Screen    None tt v_s (Logic.eq_refl _)
  ; fun s => Spawn _ _ _ CFGD _ IENVD UserInput None tt v_u (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT KSTD CFGD :=
  (fun m cfd =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with

    | Input => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD CFGD m d) envd (
         let (input, _) := pl in fun st0 =>
         if fd_eq cfd (shvec_ith (n := projT1 KSTD) _
                                 (projT2 KSTD) (kst _ _ _ st0) userinput)
         then
           [ fun s => Send PAYD COMPT KSTD CFGD _ envd
                           (StVar _ KSTD m _ curtab) Input
                           (SLit _ _ m _  input, tt) ]
         else
           []
       )

    | Display => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD CFGD m d) envd (
         let (url, _) := pl in fun st0 =>
         if fd_eq cfd (shvec_ith (n := projT1 KSTD) _
                                 (projT2 KSTD) (kst _ _ _ st0) curtab)
         then
           [ fun s => Send PAYD COMPT KSTD CFGD _ envd
                           (StVar _ KSTD m _ screen) Display
                           (SLit _ _ m _ url, tt) ]
         else
           []
       )

    | Quit => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT KSTD CFGD m d) envd (
         let _ := pl in fun st0 =>
         if fd_eq cfd (shvec_ith (n := projT1 KSTD) _
                                 (projT2 KSTD) (kst _ _ _ st0) userinput)
         then
           [ fun s => Send PAYD COMPT KSTD CFGD _ envd
                           (StVar _ KSTD m _ curtab) Quit tt
           ; fun s => Send PAYD COMPT KSTD CFGD _ envd
                           (StVar _ KSTD m _ screen) Quit tt
           ]
         else
           []
       )

    | Some (Some (Some bad)) => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD COMPT COMPS NB_CFGD CFGD INIT HANDLERS).
