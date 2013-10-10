Require Import Kernel NIExists Reflex ReflexBase ReflexFin ReflexHVec.

Import SystemFeatures.

Definition clblr (d:str) (ct:COMPT) :
  option (shvec sdenote_desc_conc_pat
    (projT2 (comp_conf_desc COMPT COMPS ct))) :=
  match ct with
  | Tab => Some (Some d, tt)
  | CProc => Some (Some d, tt)
  | UserInput => Some tt
  | _ => None
  end.

Definition vlblr (f : fin (projT1 KSTD)) := true.

Local Opaque str_of_string.

Import Language Spec.

  Ltac destruct_msg' :=
  match goal with
  | [ m : msg _ |- _ ]
      => let tag := fresh "tag" in
         let pay := fresh "pay" in
         destruct m as [tag pay]; destruct_fin tag
  end.


Ltac destruct_comp' :=
  match goal with
  | [ c : Reflex.comp _ _ |- _ ]
      => let ct := fresh "ct" in
         let cfd := fresh "cfd" in
         let cfg := fresh "cfg" in
         destruct c as [ct cfd cfg];
         destruct ct
  end.

Require Import PruneFacts.

Theorem ni : forall d, NI PAYD COMPT COMPTDEC COMPS
  IENVD KSTD INIT HANDLERS (clblr d) vlblr.
Proof.
  intros. apply ni_suf_all.

Local Opaque cmd_ok_low.
Ltac low_solve :=
  repeat first
        [ apply nop_low |
          apply seq_low |
          apply ite_low |
          apply complkup_low |
          apply call_low |
          apply send_low_ccomp |
          apply stupd_low |
          solve [auto] ].
    Time unfold low_ok''; intros; destruct_msg'; destruct_comp'; simpl;
      try discriminate; low_solve. admit. admit. admit. admit.

Ltac high_solve :=
  repeat first
    [ apply nop_high_all |
      apply seq_high_all |
      apply ite_high_all |
      apply complkup_high_all |
      apply call_high_all |
      apply spawn_high_all |
      apply send_high_all |
      apply stupd_high_all |
      solve [auto] ].

Local Opaque all_cmd_ok_high.

    Time unfold high_ok_all; intros; destruct_msg'; destruct_comp'; simpl;
      try discriminate; high_solve. simpl. unfold hdlr_tab_dom. unfold is_high_comp_pat. simpl.
      repeat first
        [ apply nop_high_all |
          apply seq_low |
          apply ite_low |
          apply complkup_low |
          apply call_low |
          apply send_low_ccomp |
          apply stupd_low |
          solve [auto] ].

  Time ni.
Qed.
