Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexHVec.
Require Import ReflexIO.
Require Import ReflexVec.

Definition splitAt c s :=
  let fix splitAt_aux c s r_res :=
    match s with
    | nil    => (List.rev r_res, nil)
    | h :: t =>
      if Ascii.ascii_dec h c then (List.rev r_res, t) else splitAt_aux c t (h :: r_res)
    end
  in splitAt_aux c s nil.

Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 11.

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
  ; ("NewTab",      [])
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
Notation NewTab      := 10%fin (only parsing).

Inductive COMPT' : Set := UserInput | Output | Tab | DomainBar.

Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition test_dir := "../test/quark/".

Definition COMPS (t : COMPT) : compd :=
  match t with
  | UserInput => mk_compd "UserInput" (test_dir ++ "user-input.py")       [] (mk_vdesc [])
  | Output    => mk_compd "Output"    (test_dir ++ "screen.py")    [] (mk_vdesc [])
  | Tab       => mk_compd "Tab"       (test_dir ++ "tab.py")     [] (mk_vdesc [str_d])
  | DomainBar => mk_compd "DomainBar" (test_dir ++ "domainbar.py") [] (mk_vdesc [])
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

Open Scope char_scope.
Definition dom {envd term} s :=
  (splitfst envd term "/" (splitsnd envd term "." s)).
Close Scope char_scope.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  seq (spawn _ IENVD Output    tt                   i_output    (Logic.eq_refl _)) (
  seq (spawn _ IENVD Tab       (default_domain, tt) i_curtab    (Logic.eq_refl _)) (
  seq (spawn _ IENVD UserInput tt                   i_userinput (Logic.eq_refl _)) (
  seq (sendall _ IENVD (mk_comp_pat _ _ Tab (None, tt)) Go (i_slit default_url, tt)) (
  seq (stupd _ IENVD v_output (Term _ (base_term _ ) _ (Var _ IENVD i_output))) (
  seq (stupd _ IENVD v_curtab (Term _ (base_term _ ) _ (Var _ IENVD i_curtab))
  ) nop))))).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match ct as _ct, t as _t return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | _, Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some bad)))))))))) =>
    match bad with end

  | Tab, ReqSocket =>
    [[ mk_vcdesc [] :
        ite (eq ccomp (stvar v_curtab))
            (
              ite (eq (dom (mvar ReqSocket None)) (cconf Tab None))
                  (
                    nop
                  )
                  (
                    nop
                  )
            ) 
            ( 
              nop
            )
    ]]
  | Tab, Display =>
      [[ mk_vcdesc [] :
         ite (eq ccomp (stvar v_curtab))
             (
               send (stvar v_output) Display (mvar Display None, tt)
             )
             (
               nop
             )
       ]]
  | Tab, ReqResource =>
      let envd := mk_vcdesc [Desc _ fd_d] in
      [[ envd :
         ite (eq (dom (mvar ReqResource None)) (cconf Tab None))
             (
               seq (call _ envd (slit (str_of_string (test_dir ++ "wget.py")))
                                 [mvar ReqResource None] None (Logic.eq_refl _))
                   (send ccomp ResResource (envvar envd None, tt))
                  
             )
             (
               nop
             )
       ]]
  | UserInput, KeyPress =>
      [[ mk_vcdesc [] :
      seq (send (stvar v_curtab) KeyPress (mvar KeyPress None, tt))
      nop ]]
  | UserInput, MouseClick =>
      [[ mk_vcdesc [] :
      seq (send (stvar v_curtab) MouseClick (mvar MouseClick None, tt))
      nop ]]
  | UserInput, NewTab =>
      let envd := mk_vcdesc [Comp _ Tab] in
      [[ envd :
         seq (spawn _ envd Tab (default_domain, tt) None (Logic.eq_refl _)) (
         seq (stupd _ envd v_curtab (envvar envd None)) (
         seq (send (stvar v_curtab) Go (slit default_url, tt))
             nop))
      ]]
  | _, _ =>
    [[ mk_vcdesc [] : nop ]]
  end.
Close Scope hdlr.
(*Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
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
                                    (Some (comp_fd s##v_output%kst))
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
                            (comp_conf (st0##v_curtab%kst))
                            None
                        )
              then
                [ fun s => spawn envd _ Tab (dom url, tt) None (Logic.eq_refl _)
                ; fun s => stupd envd _ v_curtab (envvar envd None)
                ; fun s => sendall envd _
                             (mk_comp_pat
                                Tab
                                (Some (comp_fd s##v_curtab%kst))
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
         (
           nop
         )
       end

    end (pay PAYD m)
  ).
*)


Require Import NIExists.

Open Scope char_scope.
Definition dom' s :=
  let url_end := snd (splitAt "." s) in
  fst (splitAt "/" url_end).
Close Scope char_scope.

Definition clblr d (c : comp COMPT COMPS) :=
  match c
  with
  | Build_comp Tab _ cfg =>
    let cfgd := comp_conf_desc COMPT COMPS Tab in
    if str_eq (dom' (@shvec_ith _ _ (projT1 cfgd) (projT2 cfgd)
                               cfg None)) d
    then true
    else false
  | Build_comp UserInput _ _ => true
  | _ => false
  end.

Definition vlblr (f : fin (projT1 KSTD)) := true.

Local Opaque str_of_string.

Theorem ni : forall d, NI PAYD COMPT COMPTDEC COMPS
  IENVD KSTD INIT HANDLERS (clblr d) vlblr.
Proof.
  ni.
Qed.

End Spec.

Module Main := MkMain(Spec).
Import Main.