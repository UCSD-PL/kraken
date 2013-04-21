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

Notation Display     := 0%fin (only parsing).
Notation Navigate    := 1%fin (only parsing).
Notation ReqResource := 2%fin (only parsing).
Notation ResResource := 3%fin (only parsing).
Notation ReqSocket   := 4%fin (only parsing).
Notation ResSocket   := 5%fin (only parsing).
Notation SetDomain   := 6%fin (only parsing).
Notation KeyPress    := 7%fin (only parsing).
Notation MouseClick  := 8%fin (only parsing).
Notation Go          := 9%fin (only parsing).

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
     match ct, tag PAYD m as _tm return
       @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
     with

     | Tab, Display => fun pl =>
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

     | Tab, Navigate => fun pl =>
       let envd := mk_vcdesc [Comp _ Tab] in
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
              then
                [ fun s => spawn envd _ Tab (dom url, tt) None (Logic.eq_refl _)
                ; fun s => stupd envd _ v_curtab (envvar envd None)
                ; fun s => sendall envd _
                             (mk_comp_pat
                                Tab
                                (Some (comp_fd s#v_curtab%kst))
                                (None, tt)
                             )
                             Go (slit url, tt)
                ]
              else
                []
            else
              []
         )
       end

     | Tab, ReqResource => fun pl =>
       let envd := mk_vcdesc [] in
       match pl with (url, _) =>
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           [ (* need call *)
           ]
         )
       end

     | Tab, ReqSocket => fun pl =>
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
              then
                [ (* need connect *)
                ]
              else
                []
            else
              []
         )
       end

     | UserInput, KeyPress => fun pl =>
       let envd := mk_vcdesc [] in
       match pl with (key, _) =>
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           [ fun s => sendall envd _
                              (mk_comp_pat
                                 Tab
                                 (Some (comp_fd s#v_curtab%kst))
                                 (None, tt)
                              )
                              KeyPress (slit key, tt)
           ]
         )
       end

     | UserInput, MouseClick => fun pl =>
       let envd := mk_vcdesc [] in
       match pl with (pos, _) =>
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           [ fun s => sendall envd _
                              (mk_comp_pat
                                 Tab
                                 (Some (comp_fd s#v_curtab%kst))
                                 (None, tt)
                              )
                              MouseClick (slit pos, tt)
           ]
         )
       end

     | _, Some (Some (Some (Some (Some (Some (Some (Some (Some (Some  bad))))))))) => fun _ =>
       match bad with end

     | _, _ => fun pl =>
       let envd := mk_vcdesc [] in
       existT
         (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc m d) envd
         (fun st0 =>
           []
         )

    end (pay PAYD m)
  ).

End Spec.

Module Main := MkMain(Spec).
Import Main.
