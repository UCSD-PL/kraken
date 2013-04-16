Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexHVec.
Require Import ReflexVec.

Definition splitAt c s :=
  let fix splitAt_aux c s r_res :=
    match s with
    | nil    => (List.rev r_res, nil)
    | h :: t =>
      if Ascii.ascii_dec h c then (List.rev r_res, t) else splitAt_aux c t (h :: r_res)
    end
  in splitAt_aux c s nil.

Definition dom s :=
  let url_end := snd (splitAt "." s) in
  fst (splitAt "/" url_end).

Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 10.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ ("Display",     [str_d])
  ; ("Navigate",    [str_d])
  ; ("ReqResource", [str_d])
  ; ("ResResource", [fd_d])
  ; ("ReqSocket",   [str_d])
  ; ("ResSocket",   [fd_d])
  ; ("SetDomain",   [str_d])
  ; ("KeyPress",    [str_d])
  ; ("MouseClick",  [str_d])
  ; ("Go",          [str_d])
  ].

Notation Display     := (None) (only parsing).
Notation Navigate    := (Some None) (only parsing).
Notation ReqResource := (Some (Some None)) (only parsing).
Notation ResResource := (Some (Some (Some None))) (only parsing).
Notation ReqSocket   := (Some (Some (Some (Some None)))) (only parsing).
Notation ResSocket   := (Some (Some (Some (Some (Some None))))) (only parsing).
Notation SetDomain   := (Some (Some (Some (Some (Some (Some None)))))) (only parsing).
Notation KeyPress    := (Some (Some (Some (Some (Some (Some (Some None))))))) (only parsing).
Notation MouseClick  := (Some (Some (Some (Some (Some (Some (Some (Some None)))))))) (only parsing).
Notation Go          := (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))) (only parsing).

Inductive COMPT' : Set := UserInput | Output | Tab | DomainBar.

Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | UserInput => mk_compd "UserInput" "tab.py"       [] (mk_vdesc [])
  | Output    => mk_compd "Output"    "output.py"    [] (mk_vdesc [])
  | Tab       => mk_compd "Tab"       "input.py"     [] (mk_vdesc [str_d])
  | DomainBar => mk_compd "DomainBar" "domainbar.py" [] (mk_vdesc [])
  end.

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Output; Comp _ Tab; Comp _ UserInput ].

Notation i_output    := (None) (only parsing).
Notation i_curtab    := (Some None) (only parsing).
Notation i_userinput := (Some (Some None)) (only parsing).

Definition KSTD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Output; Comp _ Tab ].

Notation v_output := (None) (only parsing).
Notation v_curtab := (Some None) (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Definition default_domain := str_of_string "google.com".
Definition default_url := str_of_string "http://www.google.com".

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  [ fun s => spawn IENVD _ Output    tt                   i_output    (Logic.eq_refl _)
  ; fun s => spawn IENVD _ Tab       (default_domain, tt) i_curtab    (Logic.eq_refl _)
  ; fun s => spawn IENVD _ UserInput tt                   i_userinput (Logic.eq_refl _)
  ; fun s => sendall IENVD _
                     (mk_comp_pat
                        Tab
                        (Some (comp_fd s#i_curtab%ienv))
                        (None, tt)
                     )
                     Go (i_slit default_url, tt)
  ; fun s => stupd IENVD _ v_output (Term _ (base_term _ IENVD) (Var _ IENVD i_output))
  ; fun s => stupd IENVD _ v_curtab (Term _ (base_term _ IENVD) (Var _ IENVD i_curtab))
  ].

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  (fun m cc =>
     let (ct, cf, cconf) := cc in
     match tag PAYD m as _tm return
       @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
     with

     | Display     => fun pl =>
       let envd := mk_vcdesc [] in
       match pl with (disp, _) =>
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
            if fd_eq cf (comp_fd (kst_ith st0 v_curtab))
            then
              [ fun s => sendall envd _
                                 (mk_comp_pat
                                    Tab
                                    (Some (comp_fd s#v_output%kst))
                                    (None, tt)
                                 )
                                 Display (slit disp, tt)
              ]
            else
              []
         )
       end

     | Navigate    => fun pl =>
       let envd := mk_vcdesc [] in
       match pl with (url, _) =>
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
            if fd_eq cf (comp_fd (kst_ith st0 v_curtab))
            then
              if str_eq (dom url)
                        (
                          shvec_ith (n := (projT1 (compd_conf (COMPS Tab))))
                            sdenote_desc
                            (projT2 (compd_conf (COMPS Tab)))
                            (comp_conf (st0#v_curtab%kst))
                            None
                        )
              then []
              else []
            else []
         )
       end

     | ReqResource => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

     | ResResource => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

     | ReqSocket   => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

     | ResSocket   => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

     | SetDomain   => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

     | KeyPress    => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

     | MouseClick  => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

     | Go          => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

     | Some (Some (Some (Some (Some (Some (Some (Some (Some (Some  bad))))))))) => fun _ =>
       match bad with end
    end (pay PAYD m)
  ).

End Spec.

Module Main := MkMain(Spec).
Import Main.
