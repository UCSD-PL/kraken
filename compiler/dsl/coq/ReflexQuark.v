Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexHVec.
Require Import ReflexVec.

Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 3.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ ("Input",   [str_d])
  ; ("Display", [str_d])
  ; ("Quit",    [ ])
  ].

Notation Input   := (None) (only parsing).
Notation Display := (Some None) (only parsing).
Notation Quit    := (Some (Some None)) (only parsing).

Inductive COMPT' : Set := Tab | Screen | UserInput.

Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Tab       => mk_compd "Tab"       "test/quark/tab.py"        [] (mk_vdesc [str_d])
  | Screen    => mk_compd "Screen"    "test/quark/screen.py"     [] (mk_vdesc [])
  | UserInput => mk_compd "UserInput" "test/quark/user-input.py" [] (mk_vdesc [])
  end.

Definition IENVD : vdesc := mk_vdesc
  [ fd_d (* curtab *)
  ; fd_d (* screen *)
  ; fd_d (* userinput *)
  ].

Definition KSTD : vdesc := mk_vdesc
  [ fd_d (* curtab *)
  ; fd_d (* screen *)
  ; fd_d (* user-input *)
  ].

Notation curtab    := (None) (only parsing).
Notation screen    := (Some None) (only parsing).
Notation userinput := (Some (Some None)) (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Definition default_domain := str_of_string "google.com".

Module Spec : SpecInterface.

Module FEATURES := SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  [ fun s => spawn IENVD _ Tab       (default_domain, tt) None (Logic.eq_refl _)
  ; fun s => spawn IENVD _ Screen    tt                   None (Logic.eq_refl _)
  ; fun s => spawn IENVD _ UserInput tt                   None (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  (fun m cc =>
     let (_, cf, _) := cc in
     match tag PAYD m as _tm return
       @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
     with

     | Input => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd (
         let (input, _) := pl in fun st0 =>
         if fd_eq
              cf
              (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD) (kst _ _ _ _ st0) userinput)
         then
           [ fun s => sendall envd _ 
                       (Build_comp_pat COMPT' COMPS Tab
                         (Some (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD)
                                          (kst _ _ _ _ st0) curtab))
                         (None, tt))
                       Input (slit input, tt)
           ]
         else
           []
       )

     | Display => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd (
         let (url, _) := pl in fun st0 =>
         if fd_eq
              cf
              (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD) (kst _ _ _ _ st0) curtab)
         then
           [ fun s => sendall envd _ 
                       (Build_comp_pat COMPT' COMPS Screen
                         (Some (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD)
                                          (kst _ _ _ _ st0) screen))
                         tt)
                       Display (slit url, tt)
           ]
         else
           []
       )

     | Quit => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd (
         let _ := pl in fun st0 =>
         if fd_eq
              cf
              (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD) (kst _ _ _ _ st0) userinput)
         then
           [ fun s => sendall envd _ 
                       (Build_comp_pat COMPT' COMPS Tab
                         (Some (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD)
                                          (kst _ _ _ _ st0) curtab))
                         (None, tt))
                       Quit tt
           ; fun s => sendall envd _ 
                       (Build_comp_pat COMPT' COMPS Screen
                         (Some (shvec_ith (n := projT1 KSTD) _ (projT2 KSTD)
                                          (kst _ _ _ _ st0) screen))
                         tt)
                       Quit tt
           ]
         else
           []
       )

     | Some (Some (Some bad)) => fun _ =>
       match bad with end
    end (pay PAYD m)
  ).

End Spec.

Module Main := MkMain(Spec).
Import Main.
