Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexHVec.
Require Import ReflexIO.
Require Import ReflexFacts.
Require Import NIExists.
Require Import Ynot.
Require Import PruneFacts.
Require Import Decidable.
Require Import List.
Require Import ActionMatch.
Require Import PolLang.

Module Type SystemFeaturesInterface.
  Parameter NB_MSG   : nat.
  Parameter PAYD     : vvdesc NB_MSG.
  Parameter COMPT    : Set.
  Parameter COMPTDEC : forall (x y : COMPT), decide (x = y).
  Parameter COMPS    : COMPT -> compd.
  Parameter IENVD    : vcdesc COMPT.
  Parameter KSTD     : vcdesc COMPT.
End SystemFeaturesInterface.

Module MkLanguage (Import SF : SystemFeaturesInterface).
  Instance SDenoted_cdesc : SDenoted (cdesc COMPT) := SDenoted_cdesc COMPT COMPS.
  Definition seq {envd term} := Seq PAYD COMPT COMPS KSTD envd term.
  Definition nop {envd term} := Nop PAYD COMPT COMPS KSTD envd term.
  Definition ite {envd term} := Ite PAYD COMPT COMPS KSTD envd term.
  Definition send {envd term ct} := Reflex.Send PAYD COMPT COMPS KSTD envd term ct.
  Definition spawn := Spawn PAYD COMPT COMPS KSTD.
  Definition call := Reflex.Call PAYD COMPT COMPS KSTD.
  Definition stupd := StUpd PAYD COMPT COMPS KSTD.
  Definition complkup {term envd}:= CompLkup PAYD COMPT COMPS KSTD term envd.

  Definition stvar {cc envd m} v :=
    Term COMPT COMPS (hdlr_term PAYD COMPT COMPS KSTD cc m) envd (StVar _ _ _ _ _ _ _ v).
  Definition i_envvar envd i :=
    Term COMPT COMPS (base_term _) envd (Var _ envd i).
  Definition envvar {cc m} envd i :=
    Term COMPT COMPS (hdlr_term PAYD COMPT COMPS KSTD cc m) envd
         (Base _ _ _ _ _ _ _ (Var _ envd i)).
  Definition slit {cc envd m} v :=
    Term COMPT COMPS (hdlr_term PAYD COMPT COMPS KSTD cc m) envd (Base _ _ _ _ _ _ _ (SLit _ _ v)).
  Definition nlit {cc envd m} v :=
    Term COMPT COMPS (hdlr_term PAYD COMPT COMPS KSTD cc m) envd (Base _ _ _ _ _ _ _ (NLit _ _ v)).
  Definition ccomp {cc envd m} :=
    Term COMPT COMPS (hdlr_term PAYD COMPT COMPS KSTD cc m) envd (CComp _ _ _ _ _ _ _).
  Definition i_slit v := Term COMPT COMPS (base_term _) IENVD (SLit _ _ v).
  Definition i_nlit v := Term COMPT COMPS (base_term _) IENVD (NLit _ _ v).
  Definition mk_comp_pat := Build_comp_pat COMPT COMPS.

(*
  Definition comp_fd {envd ct} ce (*{ct : COMPT} (x : sigT (fun c => comp_type COMPT COMPS c = ct))*)
    := CompFd COMPT envd ct ce.*)
  Definition comp_conf {ct : COMPT} (x : sigT (fun c => comp_type COMPT COMPS c = ct))
  : s[[ comp_conf_desc COMPT COMPS ct ]]
    :=
      match projT2 x in _ = _ct return s[[ comp_conf_desc COMPT COMPS _ct ]] with
      | Logic.eq_refl => comp_conf COMPT COMPS (projT1 x)
      end.

  Definition i_env_ith s i :=
    shvec_ith (n := projT1 IENVD) (sdenote_cdesc COMPT COMPS) (projT2 IENVD)
              (init_env PAYD COMPT COMPS KSTD IENVD s) i.
  Notation "s ## i" := (i_env_ith s i) (at level 0) : ienv.
  Delimit Scope ienv with ienv.

  Definition env_ith {ENVD : vcdesc COMPT} s i :=
    shvec_ith (n := projT1 ENVD) (sdenote_cdesc COMPT COMPS) (projT2 ENVD)
              (hdlr_env PAYD COMPT COMPS KSTD ENVD s) i.
  Notation "s ## i" := (env_ith s i) (at level 0) : env.
  Delimit Scope env with env.

  Definition kst_ith s i :=
    shvec_ith (n := projT1 KSTD) (sdenote_cdesc COMPT COMPS) (projT2 KSTD)
              (kst PAYD COMPT COMPS KSTD s) i.
  Notation "s ## i" := (kst_ith s i) (at level 0) : kst.
  Delimit Scope kst with kst.

  Definition eq {term d envd} e1 e2 :=
    BinOp COMPT COMPS term envd
          (Eq _ _ d) e1 e2.

  Definition splitfst envd term c s :=
    UnOp COMPT COMPS term envd (SplitFst _ _ c) s.

  Definition splitsnd envd term c s :=
    UnOp COMPT COMPS term envd (SplitSnd _ _ c) s.

  Definition unop_num envd term (d:cdesc COMPT) (op:s[[d]] -> num) e :=
    UnOp COMPT COMPS term envd (UnopNum COMPT COMPS d op) e.

  Definition unop_str envd term (d:cdesc COMPT) (op:s[[d]] -> str) e :=
    UnOp COMPT COMPS term envd (UnopStr COMPT COMPS d op) e.

  Definition binop_num envd term (d1 d2:cdesc COMPT)
             (op:s[[d1]] -> s[[d2]] -> num) e1 e2 :=
    BinOp COMPT COMPS term envd (BinopNum COMPT COMPS d1 d2 op) e1 e2.

  Definition binop_str envd term (d1 d2:cdesc COMPT)
             (op:s[[d1]] -> s[[d2]] -> str) e1 e2 :=
    BinOp COMPT COMPS term envd (BinopStr COMPT COMPS d1 d2 op) e1 e2.

  Definition mvar
  {envd} (t : fin NB_MSG) {ct} i :=
  (Term COMPT COMPS _ _ (MVar PAYD COMPT COMPS KSTD ct t envd i)).

  Definition cconf
  {envd} {t : fin NB_MSG} ct ct' i ce :=
  (Term COMPT COMPS _ _ (CConf PAYD COMPT COMPS KSTD ct t envd ct' i ce)).

(*Unfortunately, I need to put tactics here because one of them
  must refer to ite in a match.*)
Ltac destruct_fin f :=
  match type of f with
  | False => destruct f
  | _ => let f' := fresh "f" in
         destruct f as [ f' | ]; [destruct_fin f' | ]
  end.

Ltac destruct_pay pay :=
  compute in pay;
  match type of pay with
  | unit => idtac
  | _ => let a := fresh "a" in
         let b := fresh "b" in
         destruct pay as [a b]; simpl in a; destruct_pay b
  end.

Ltac destruct_msg :=
  match goal with
  | [ m : msg _ |- _ ]
      => let tag := fresh "tag" in
         let pay := fresh "pay" in
         destruct m as [tag pay]; destruct_fin tag;
         destruct_pay pay
  end.


Ltac destruct_comp :=
  match goal with
  | [ c : Reflex.comp _ _ |- _ ]
      => let ct := fresh "ct" in
         let cfd := fresh "cfd" in
         let cfg := fresh "cfg" in
         destruct c as [ct cfd cfg];
         destruct ct; destruct_pay cfg
  end.

Ltac remove_redundant_ktr :=
  unfold NIExists.ktr in *;
  match goal with
  | [ H : Reflex.ktr _ _ _ _ ?s = inhabits ?tr,
      H' : Reflex.ktr _ _ _ _ ?s = inhabits ?tr' |- _ ]
    => rewrite H' in H; apply pack_injective in H; subst tr
  end.

Ltac uninhabit :=
  match goal with
  | [ H : inhabits _ = inhabits ?tr |- _ ]
    => apply pack_injective in H; subst tr
  end.

Ltac subst_inter_st :=
  match goal with
  | [ _ : ?s = mk_inter_ve_st _ _ _ _ _ _ _ _ |- _ ]
    => subst s
  end.

Ltac destruct_comp_var :=
  match goal with
  | [ cp : sigT (fun (c : Reflex.comp _ _) => _) |- _ ]
    => let pf := fresh "pf" in
       let ct := fresh "ct" in
       let f := fresh "f" in
       let cfg := fresh "cfg" in
       destruct cp as [ [ct f cfg] pf];
       destruct ct; try discriminate
       (*discriminate prunes impossible ctypes*)
  end.

Ltac destruct_kstate pay :=
  match type of pay with
  | unit => idtac
  | _ => let a := fresh "a" in
         let b := fresh "b" in
         destruct pay as [a b]; simpl in a; destruct_pay b
  end.

Ltac destruct_state :=
  match goal with
  |- context[kst _ _ _ _ ?s]
    => let kvars := fresh "kvars" in
       set (kvars:=kst _ _ _ _ s);
       destruct_kstate kvars;
       repeat destruct_comp_var; simpl
  end.

Ltac destruct_cond :=
match goal with
|- context[ if ?e then _ else _ ] => destruct e
end.

Ltac destruct_find_comp :=
  match goal with
  |- context[match find_comp ?a ?b ?c ?d ?e with | Some _ => _ | None => _ end ]
    => let Heq := fresh "Heq" in
       destruct (find_comp a b c d e) as [? | ?]_eqn:Heq; try rewrite Heq;
       [apply find_comp_suc_match with (cp:=d) in Heq | ]
  end.

Ltac destruct_comp_pf :=
  match goal with
  | [ cpf : sigT (fun _ : Reflex.comp _ _ => _ = _ ) |- _ ]
    => destruct cpf; destruct_comp
  end.

Ltac destruct_atom_eqs :=
  repeat match goal with
         | [ _ : context [str_eq ?a ?b] |- _ ]
           => destruct (str_eq a b)
         | [ |- context [str_eq ?a ?b] ]
           => destruct (str_eq a b)
         | [ _ : context [num_eq ?a ?b] |- _ ]
           => destruct (num_eq a b)
         | [ |- context [num_eq ?a ?b] ]
           => destruct (num_eq a b)
         | [ _ : context [fd_eq ?a ?b] |- _ ]
           => destruct (fd_eq a b)
         | [ |- context [fd_eq ?a ?b] ]
           => destruct (fd_eq a b)
         end.

Ltac find_comp_tr_solve :=
  repeat destruct_comp_pf; try discriminate;
  unfold Reflex.match_comp, Reflex.match_comp_pf in *; simpl in *;
  destruct_atom_eqs; try discriminate; try congruence.

Ltac find_comp_eq :=
  match goal with
  | [ _ : vars_eq _ _ _ _ ?s1 ?s2 _ |-
    context[match find_comp _ _ _ _ (kcs _ _ _ _ ?s1) with | Some _ => _ | None => _ end] ]
    => unfold eval_hdlr_comp_pat, eval_hdlr_payload_oexpr, eval_payload_oexpr; simpl;
       erewrite hout_eq_find_eq with (s':=s2); eauto;
       match goal with
       | [ |- high_comp_pat _ _ _ _ _ ]
         => solve [unfold high_comp_pat, Reflex.match_comp, match_comp_pf; intros;
            destruct_comp; try discriminate; simpl in *;
            destruct_atom_eqs; try discriminate; try congruence]
       | [ |- high_out_eq _ _ _ _ _ _ _ /\ vars_eq _ _ _ _ _ _ _ ]
         => idtac
       | [ |- high_out_eq _ _ _ _ _ _ _ ]
         => idtac
       | [ |- vars_eq _ _ _ _ _ _ _ ]
         => idtac
       end
  end.

Ltac vars_eq_tac :=
  match goal with
  | [ Hvars :  vars_eq _ _ _ _ _ _ _ |- _ ]
    => solve [ unfold vars_eq; simpl; auto
      | unfold vars_eq; simpl; inversion Hvars; auto ]
  end.

Ltac state_var_branch :=
  match goal with
  | [ Hout : high_out_eq _ _ _ _ ?s1 ?s2 _,
      Hvars : vars_eq _ _ _ _ ?s1 ?s2 _ |- _ ]
    => match goal with
       | [ _ : Reflex.ktr _ _ _ _ s1 = inhabits ?tr1,
           _ : Reflex.ktr _ _ _ _ s2 = inhabits ?tr2 |- _ ]
         => try rewrite Hout with (tr:=tr1) (tr':=tr2); auto;
            inversion Hvars; auto;
            (*rewrite any equalities created by inverting Hvars*)
            repeat match goal with
                   | [ Heq : ?l = _ |- _ ]
                     => match l with
                        | fst ?e =>
                          match e with
                          | context [ Reflex.kst _ _ _ _ _ ] =>
                            rewrite Heq in *; clear Heq
                          end
                        end
                   end; auto; try contradiction
       end
  end.

Ltac destruct_comp_st_vars :=
  match goal with
  |- context [projT1 ?e]
    => match type of e with
       | sigT (fun _ : Reflex.comp _ _ => _ = _)
         => destruct e as [ [ct ? ?] ?]; destruct ct; try discriminate; simpl
       end
  end.

Ltac ho_eq_tac tac Hlblr :=
  unfold high_out_eq; simpl; intros;
  repeat remove_redundant_ktr;
  repeat uninhabit; simpl;
  simpl in Hlblr; try rewrite Hlblr;
  try solve[tac | destruct_cond; tac
    | state_var_branch | find_comp_tr_solve; tac
    | repeat destruct_comp_st_vars; tac ]
  (*destruct_state is expensive, so try it only as
     a last resort*).

Ltac destruct_ite :=
  match goal with
  |- context[ ite _ _ _ ]
    => unfold kstate_run_prog;
       unfold hdlr_state_run_cmd; simpl;
       repeat destruct_cond
  end.

Ltac ho_eq_solve_low :=
  simpl; auto.

Ltac low_step :=
  unfold low_ok; intros;
  match goal with
  | [ Hve : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ ?s _,
      Hlow : _ = false |- _ ]
    => destruct_msg; destruct_comp;
       try discriminate;
       try solve [eapply prune_nop_1; eauto];
       inversion Hve; repeat subst_inter_st; 
       unfold kstate_run_prog; simpl;
       repeat destruct_find_comp; repeat destruct_cond;
       split;
       try abstract (
       match goal with
       | [ |- high_out_eq _ _ _ _ _ _ _ ]
         => ho_eq_tac ho_eq_solve_low Hlow
       | [ |- vars_eq _ _ _ _ _ _ _ ]
         => auto
       | _ => idtac
       end)
  end.

Ltac ho_eq_solve_high :=
  repeat match goal with
         | [ |- _::_ = _::_ ] => f_equal; auto
         | _ => auto
         end.

Ltac high_steps :=
  unfold high_ok; intros;
  match goal with
  | [ Hve1 : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ ?s1 _,
      Hve2 : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ ?s2 _,
      Hhigh : _ = true |- _ ]
    => destruct_msg; destruct_comp;
       try discriminate;
       try solve [eapply prune_nop_2; eauto];
       inversion Hve1; inversion Hve2;
       repeat subst_inter_st; unfold kstate_run_prog;
       simpl;
       repeat find_comp_eq; repeat destruct_find_comp;
       repeat destruct_cond;
       split;
       try abstract (
       match goal with
       | [ |- high_out_eq _ _ _ _ _ _ _ ]
         => ho_eq_tac ho_eq_solve_high Hhigh
       | [ |- vars_eq _ _ _ _ _ _ _ ]
         => vars_eq_tac
       | _ => idtac
       end)
  end.

Ltac ni :=
  intros; apply ni_suf; [low_step | high_steps].

(*Policy language tactics*)

Ltac destruct_ite_pol :=
  match goal with
  |- context[ ite _ _ _ ]
    => unfold kstate_run_prog in *;
       unfold hdlr_state_run_cmd in *; simpl in *;
       repeat destruct_cond
  end.

Ltac unpack :=
  match goal with
  | [ H : Reflex.InitialState _ _ _ _ _ _ _ _ ?s |- _ ]
    => inversion H;
       match goal with
       | [ _ : ?s' = init_state_run_cmd _ _ _ _ _ _ _ _ _ |- _ ]
         => subst s'; subst s
       end
  | [ H : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ ?s |- _ ]
    => destruct_msg; destruct_comp; inversion H;
       match goal with
       | [ _ : ?s' = mk_inter_ve_st _ _ _ _ _ _ _ _ |- _ ]
         => subst s'; subst s
       end
  | [ H : Reflex.BogusExchange _ _ _ _ _ _ _ ?s |- _ ]
    => inversion H; subst s
  end; simpl; unfold kstate_run_prog in *; simpl in *;
       repeat destruct_find_comp; repeat destruct_cond;
       simpl in *; intros; try uninhabit.

Ltac clear_useless_hyps :=
  repeat match goal with
         | [ s : Reflex.kstate _ _ _ _ |- _ ]
           => match goal with
              | [ H : s = _ |- _ ]
                => clear H
              | [ H : _ = s |- _ ]
                => clear H
              end
         | [ H : _ = _ |- _ ]
           => revert H
         | [ H : _ <> _ |- _ ]
           => revert H
         | [ H : Reflex.Reach _ _ _ _ _ _ _ _ _ |- _ ]
           => revert H
         | [ H : In _ _ |- _ ]
           => revert H
         | _
           => idtac
         end; clear; intros.

Ltac destruct_unpack :=
  match goal with
  | [ m : msg _ |- _ ]
      => destruct_msg; unpack
  | _
      => unpack
  end.

Ltac subst_states :=
  repeat match goal with
         | [ s : kstate _ _ _ _ |- _ ]
             => match goal with
                | [ _ : s = _ |- _ ]
                    => subst s
                end
         | [ s : init_state _ _ _ _ _ |- _ ]
             => match goal with
                | [ _ : s = _ |- _ ]
                    => subst s
                end
         end.

Ltac subst_assignments :=
  repeat match goal with
         | [ a := _ |- _ ]
           => subst a
         end.

Lemma and_not_decide : forall P Q, decide P -> ~(P /\ Q) -> ~P \/ ~Q.
intros P Q dP H.
apply not_and in H.
auto.
unfold decidable; destruct dP; auto.
Qed.

Ltac get_decide P :=
  match P with
  | ?a = _ => match type of a with
             | str => apply str_eq
             | num => apply num_eq
             | fd => apply fd_eq
             end
  | _ => auto
  end.

Ltac destruct_neg_conjuncts H :=
  match type of H with
  | ~(?P /\ _) => let R := fresh "R" in
                  apply and_not_decide in H;
                  [ destruct H as [ | R ];
                    [ | destruct_neg_conjuncts R ] | get_decide P ]
  | _ => idtac
  end.

Ltac destruct_action_matches :=
  repeat match goal with
         | [ H : ActionMatch.AMatch _ _ _ _ ?future ?act |- _ ]
           => simpl in H; unfold msgMatch, msgMatch' in H;
              simpl in H (*maybe produces a conjunction of Props*);
              decompose [and] H
         | [ H : ~ActionMatch.AMatch _ _ _ _ ?future ?act |- _ ]
           => simpl in H; unfold msgMatch, msgMatch' in H; simpl in H
              (*maybe produces a negated conjunction of decidable Props*);
              destruct_neg_conjuncts H
         end.

Lemma cut_exists : forall nb_msg plt compt comps act disj_R conj_R,
  (exists past : @Reflex.KAction nb_msg plt compt comps, (disj_R past) /\ (conj_R past)) ->
  exists past, (act = past \/ disj_R past) /\ (conj_R past).
Proof.
  intros nb_msg plt compt comps act disj_R conj_R H.
  destruct H.
  exists x.
  destruct H.
  auto.
Qed.

Ltac releaser_match :=
  simpl;
  repeat match goal with
         | [ |- exists past : Reflex.KAction _ _ _, (?act = _ \/ ?disj_R ) /\ ?conj_R ]
           => solve [exists act; unfold msgMatch, msgMatch'; simpl; intuition; congruence] ||
              apply cut_exists
         end.

Ltac use_IH_releases :=
  match goal with
  | [ IHReach : context[ exists past : Reflex.KAction _ _ _, _ ] |- _ ]
    => repeat apply cut_exists; apply IHReach; auto
  end.

Ltac reach_induction :=
  intros;
  match goal with
  | [ _ : Reflex.ktr _ _ _ _ _ = inhabits ?tr, H : Reflex.Reach _ _ _ _ _ _ _ _ _ |- _ ]
      => generalize dependent tr; induction H; unpack
         (*Do not put simpl anywhere in here. It breaks destruct_unpack.*)
  end.

Ltac impossible :=
  try discriminate; try contradiction;
  match goal with
  | [ H : _ = _ |- _ ] => contradict H; solve [auto]
  | [ H : _ <> _ |- _ ] => contradict H; solve [auto]
  end.

Ltac destruct_comp_var_pay :=
  match goal with
  | [ cp : sigT (fun (c : Reflex.comp _ _) => _) |- _ ]
    => let pf := fresh "pf" in
       let ct := fresh "ct" in
       let f := fresh "f" in
       let cfg := fresh "cfg" in
       destruct cp as [ [ct f cfg] pf];
       destruct ct; try discriminate; destruct_pay cfg
       (*discriminate prunes impossible ctypes*)
  end.

Ltac extract_match_facts :=
  repeat destruct_comp_var_pay; unfold Reflex.match_comp, Reflex.match_comp_pf in *;
  simpl in *; destruct_atom_eqs; try discriminate; simpl in *.

Ltac exists_past :=
  destruct_action_matches;
  extract_match_facts;
  (*There may be conditions on s' (the intermediate state). We want
    to use these conditions to derive conditions on s.*)
  (*subst_states;*)
  (*Try to match stuff at head of trace.*)
  releaser_match;
  (*This may not clear the old induction hypothesis. Does it matter?*)
  clear_useless_hyps;
  (*Should this take s as an argument?*)
  reach_induction;
  try solve [ impossible
            | use_IH_releases
            | releaser_match
            | auto].
(*  destruct_action_matches;
  extract_match_facts;
  (*There may be conditions on s' (the intermediate state). We want
    to use these conditions to derive conditions on s.*)
  (*subst_states;*)
  (*Try to match stuff at head of trace.*)
  releaser_match;
  (*This may not clear the old induction hypothesis. Does it matter?*)
  clear_useless_hyps;
  (*Should this take s as an argument?*)
  reach_induction;
  match goal with
  | [ _ : Reflex.InitialState _ _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *;
       try solve [ impossible
                 | releaser_match ]
  | [ _ : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *;
       try solve [ impossible
                 | use_IH_releases
                 | releaser_match
                 (*| exists_past*)]
        (*destruct_eq might have created contradictions
           with previous calls of destruct_eq*)
  | [ _ : Reflex.BogusExchange _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *; use_IH_releases
  | _ => idtac
  end.*)

Ltac match_releases :=
  match goal with
  | [ |- Enables _ _ _ _ _ _ nil ]
      => constructor
  (* Induction hypothesis.*)
  | [ H : Reflex.ktr _ _ _ _ ?s = inhabits ?tr,
      IH : forall tr', Reflex.ktr _ _ _ _ ?s = inhabits tr' ->
                       Enables _ _ _ _ ?past ?future tr'
                       |- Enables _ _ _ _ ?past ?future ?tr ]
      => auto
  (*Branch on whether the head of the trace matches.*)
  | [ |- Enables ?pdv ?compt ?comps ?comptdec _ ?future (?act::_) ]
      => (*let s := match goal with
                  | [ _ : ktr _ _ _ _ ?s = inhabits _ |- _ ]
                      => s
                  | [ s : init_state _ _ _ _ _ |- _ ]
                      => s
                  end in*)
         let H := fresh "H" in
         pose proof (decide_act pdv compt comps comptdec future act) as H;
         destruct H;
         [ first [ contradiction | destruct_action_matches; contradiction |
           (apply E_future; [ match_releases | try solve [exists_past] ]) ]
         | first [ contradiction | destruct_action_matches; contradiction |
           (apply E_not_future; [ match_releases | assumption ]) ] ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  end.

Ltac use_IH_disables :=
  match goal with
  | [ IHReach : context[forall tr' : Reflex.KTrace _ _ _, _],
      _ : Reflex.ktr _ _ _ _ ?s = inhabits ?tr |- _ ]
      => apply IHReach with (tr':=tr); auto (*TODO: auto may not always work here.*)
  end.

(*This function should be passed a state. It will then attempt to prove
  that there are no instances of the disabler (should it be passed the disabler?)
  anywhere in the trace of that state.*)
(*There are two situations:
1.) The trace of the state is fully concrete: no induction required.
2.) The trace is not fully concrete: induction required.*)
Ltac forall_not_disabler :=
  destruct_action_matches;
  extract_match_facts;
(*   (*There may be conditions on s' (the intermediate state). We want
    to use these conditions to derive conditions on s.*)
  subst_states;*)
  (*This may not clear the old induction hypothesis. Does it matter?*)
  clear_useless_hyps;
  (*Should this take s as an argument?*)
  reach_induction;
  match goal with
  | [ H :  context[ List.In ?act _ ] |- _ ]
      => simpl in *; decompose [or] H;
         try solve [ impossible
                   | (subst act; tauto)
                   | use_IH_disables ]
  end.
(*
  match goal with
  | [ H : _ = init_state_run_cmd _ _ _ _ _ _ _ _ _,
          H' : context[ List.In ?act _ ] |- _ ]
    => simpl in *; subst_states;
       try solve [impossible]; simpl in H'; decompose [or] H';
       try solve [(subst act; tauto)
                 | contradiction]
       (*subst act' works when it is set equal to actual action*)
       (*contradiction works when act' is in nil*)
  | [ _ : ktr _ _ _ _ ?s' = inhabits _, H' : context[ List.In ?act _ ] |- _ ]
    => subst_assignments; subst_states; simpl in *;
       try solve [impossible];
       decompose [or] H';
       try solve [(subst act; tauto)
                 | use_IH_disables
                 | forall_not_disabler s' ]
  end.*)

Ltac match_disables :=
  match goal with
  | [ |- Disables _ _ _ _ _ _ nil ]
      => constructor
  (* Induction hypothesis.*)
  | [ H : Reflex.ktr _ _ _ _ ?s = inhabits ?tr,
      IH : forall tr', Reflex.ktr _ _ _ _ ?s = inhabits tr' ->
                       Disables _ _ _ _ ?past ?future tr'
                       |- Disables _ _ _ _ ?past ?future ?tr ]
      => auto
  (*Branch on whether the head of the trace matches.*)
  | [ |- Disables ?pdv ?compt ?comps ?comptdec _ ?future (?act::_) ]
      => let H := fresh "H" in
         let A := fresh "A" in
         pose proof (decide_act pdv compt comps comptdec future act) as H;
         destruct H as [A|A]; simpl in A; repeat autounfold in A; simpl in A;
         [ tauto ||
           (apply D_disablee; [ match_disables | forall_not_disabler])
         | tauto ||
           (apply D_not_disablee; [ match_disables | assumption ]) ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  end.

Ltac act_match :=
  simpl in *; repeat destruct_comp_st_vars; intuition.

Ltac match_immbefore :=
  match goal with
  | [ |- ImmBefore _ _ _ _ _ _ nil ]
      => constructor
  (*Induction hypothesis*)
  | [ H : Reflex.ktr _ _ _ _ ?s = inhabits ?tr,
      IH : forall tr', Reflex.ktr _ _ _ _ ?s = inhabits tr' ->
                       ImmBefore _ _ _ _ ?oact_b ?oact_a tr'
                       |- ImmBefore _ _ _ _ ?oact_b ?oact_a ?tr ]
      => auto
  | [ |- ImmBefore ?pdv ?compt ?comps ?comptdec _ ?oact_a (?act::_) ] =>
    let H := fresh "H" in
    let A := fresh "A" in
    pose proof (decide_act pdv compt comps comptdec oact_a act) as H;
    destruct H as [A|A]; simpl in A; repeat autounfold in A;
    [ tauto || (apply IB_A; [ match_immbefore | act_match ])
    | tauto || (apply IB_nA; [ match_immbefore | assumption ])
    ]
  (* In some cases, one branch is impossible, so tauto solves it
     /!\ contradiction is not powerful enough to handle ~(True /\ True)
     In other cases, there are variables in the message payloads,
     so both branches are possible.*)
  end.

Ltac match_immafter :=
  match goal with
  | [ |- ImmAfter _ _ _ _ _ _ nil ]
      => constructor
  | [ H : Reflex.ktr _ _ _ _ ?s = inhabits ?tr,
      IH : forall tr', Reflex.ktr _ _ _ _ ?s = inhabits tr' ->
                       ImmAfter _ _ _ _ ?oact_a ?oact_b tr'
                       |- ImmAfter _ _ _ _ ?oact_a ?oact_b ?tr ]
      => auto
  | [ |- ImmAfter ?pdv ?compt ?comps ?comptdec _ ?oact_b (_::?act::_) ]
      => let H := fresh "H" in
         let A := fresh "A" in
         pose proof (decide_act pdv compt comps comptdec oact_b act) as H;
         destruct H as [A|A]; simpl in A; repeat autounfold in A;
         [ tauto ||
           (apply IA_B; [ match_immafter | act_match ] )
         | tauto ||
           (apply IA_nB; [ match_immafter | act_match ] ) ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  | [ |- ImmAfter _ _ _ _ _ _ (?act::_) ]
      (*If theres only one concrete action at the head of the trace,
        it better not a before action because there's nothing after.*)
      => apply IA_nB; [ match_immafter | act_match ]
  end.

Ltac crush :=
  reach_induction;
  match goal with
  | [ |- ImmBefore _ _ _ _ _ _ _ ]
     => try abstract match_immbefore
  | [ |- ImmAfter _ _ _ _ _ _ _ ]
     => try abstract match_immafter
  | [ |- Enables _ _ _ _ _ _ _ ]
     => try match_releases
  | [ |- Disables _ _ _ _ _ _ _ ]
     => try match_disables
  end.

End MkLanguage.

Module Type SpecInterface.
  Include SystemFeaturesInterface.
  Parameter INIT : init_prog PAYD COMPT COMPS KSTD IENVD.
  Parameter HANDLERS : handlers PAYD COMPT COMPS KSTD.
End SpecInterface.

Module MkMain (Import S : SpecInterface).
  Definition main :=
    @main _ PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS.
End MkMain.

Fixpoint mk_vdesc' l : vdesc' (List.length l) :=
  match l with
  | nil     => tt
  | x :: xs => (x, mk_vdesc' xs)
  end.

Definition mk_vdesc l : vdesc := existT _ (List.length l) (mk_vdesc' l).

Fixpoint mk_vcdesc' {COMPT} l : vcdesc' COMPT (List.length l) :=
  match l with
  | nil     => tt
  | x :: xs => (x, mk_vcdesc' xs)
  end.

Definition mk_vcdesc {COMPT} l : vcdesc COMPT := existT _ (List.length l) (mk_vcdesc' l).

Fixpoint mk_vvdesc (l : list (string * list desc)) : vvdesc (List.length l) :=
  match l with
  | nil          => tt
  | (_, x) :: xs => (mk_vdesc x, mk_vvdesc xs)
  end.

Definition mk_compd name cmd args conf :=
  {| compd_name := str_of_string name
   ; compd_cmd  := str_of_string cmd
   ; compd_args := List.map str_of_string args
   ; compd_conf := conf
   |}.

Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).

Notation "<< n & e >>" := (existT _ n e)
 (n at level 59, e at level 39) : hdlr.
Notation "[[ e : c ]]" := (existT _ e c)
 (c at level 59, e at level 39) : hdlr.

Delimit Scope fin_scope with fin.

Notation "0"  := (None) : fin_scope.
Notation "1"  := (Some (None)) : fin_scope.
Notation "2"  := (Some (Some None)) : fin_scope.
Notation "3"  := (Some (Some (Some None))) : fin_scope.
Notation "4"  := (Some (Some (Some (Some None)))) : fin_scope.
Notation "5"  := (Some (Some (Some (Some (Some None))))) : fin_scope.
Notation "6"  := (Some (Some (Some (Some (Some (Some None)))))) : fin_scope.
Notation "7"  := (Some (Some (Some (Some (Some (Some (Some None))))))) : fin_scope.
Notation "8"  := (Some (Some (Some (Some (Some (Some (Some (Some None)))))))) : fin_scope.
Notation "9"  := (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))) : fin_scope.
Notation "10" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))) : fin_scope.
Notation "11" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))) : fin_scope.
Notation "12" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))) : fin_scope.
Notation "13" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))) : fin_scope.
Notation "14" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))) : fin_scope.
Notation "15" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))))) : fin_scope.
Notation "16" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))))) : fin_scope.
Notation "17" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))))))) : fin_scope.
Notation "18" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))))))) : fin_scope.
Notation "19" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))))))))) : fin_scope.
Notation "20" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))))))))) : fin_scope.
