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
Require Import PolLangFacts.
Require Import Opt.

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

  Definition lt {term envd} e1 e2 :=
    BinOp COMPT COMPS term envd (Lt _ _) e1 e2.

  Definition add {term envd} e1 e2 :=
    BinOp COMPT COMPS term envd (Add _ _) e1 e2.

  Definition cat {term envd} e1 e2 :=
    BinOp COMPT COMPS term envd (Cat _ _) e1 e2.

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
Ltac run_opt o t_on t_off :=
  match eval unfold o in o with
  | true => t_on
  | false => t_off
  end.

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

Ltac destruct_input input :=
  compute in input;
  match type of input with
  | unit => idtac
  | num => idtac
  | fd  => idtac
  | _ => let a := fresh "a" in
         let b := fresh "b" in
         destruct input as [a b]; simpl in a; destruct_input b
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

Ltac impossible :=
  try discriminate; try contradiction;
  match goal with
  | [ H : _ = _ |- _ ] => contradict H; solve [auto]
  | [ H : _ <> _ |- _ ] => contradict H; solve [auto]
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

Ltac destruct_cond' H :=
match type of H with
| context[ if ?e then _ else _ ] => destruct e
end.

Ltac destruct_find_comp :=
  let find_comp_expr :=
      match goal with
      | [ |- context[match find_comp ?a ?b ?c ?d ?e with | Some _ => _ | None => _ end ] ]
        => (constr:(find_comp a b c d e))
      | [ _ : context[match find_comp ?a ?b ?c ?d ?e with | Some _ => _ | None => _ end ] |- _ ]
        => (constr:(find_comp a b c d e))
      end in
  let Heq := fresh "Heq" in
  let Heq' := fresh "Heq'" in
  destruct find_comp_expr as [? | ?]_eqn:Heq; try rewrite Heq;
  [ pose proof (find_comp_suc_match _ _ _ _ _ _ Heq) as Heq'; destruct Heq'
  | pose proof (find_comp_fail _ _ _ _ _ Heq);
    pose proof (find_comp_fail_prop _ _ _ _ _ Heq); clear Heq ].

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

Ltac high_comp_pat_tac :=
  unfold high_comp_pat, Reflex.match_comp, match_comp_pf; intros;
  destruct_comp; try discriminate; simpl in *;
  destruct_atom_eqs;
  intuition; try discriminate; try congruence.

Ltac find_comp_eq Hs1 Hs2 :=
  match type of Hs1 with
  | context[ find_comp _ _ _ _ (Reflex.kcs _ _ _ _ ?s1) ]
    => match type of Hs2 with
       | context[ find_comp _ _ _ _ (Reflex.kcs _ _ _ _ ?s2)]
         => match goal with
            | [ _ : high_out_eq _ _ _ _ _ _ ?comp_lblr |- _ ]
              => erewrite hout_eq_find_eq1 with
                 (s':=s2) (clblr:=comp_lblr) in Hs1; eauto;
                 match goal with
                 | [ |- high_comp_pat _ _ _ _ _ ]
                     => clear Hs1 Hs2;
                       (*We have to clear these hypothesis for this goal so that
                         we can run simpl in * without worrying about performance
                         consequences.*)
                        high_comp_pat_tac; fail 1
                 | [ |- high_out_eq _ _ _ _ _ _ _ ]
                     => apply high_out_eq_sym; auto
                 | [ |- _ ]
                     => idtac
                 end
            | [ _ : cs_eq _ _ _ _ _ _ ?comp_lblr |- _ ]
              => erewrite hout_eq_find_eq2 with
                 (s':=s2) (cslblr:=comp_lblr) in Hs1; eauto;
                 match goal with
                 | [ |- high_comp_pat _ _ _ _ _ ]
                     => clear Hs1 Hs2;
                       (*We have to clear these hypothesis for this goal so that
                         we can run simpl in * without worrying about performance
                         consequences.*)
                        high_comp_pat_tac; fail 1
                 | [ |- cs_eq _ _ _ _ _ _ _ ]
                     => apply cs_eq_sym; auto
                 | [ |- _ ]
                     => idtac
                 end
            end
       end
  end.

Ltac destruct_find_comp' H :=
  match goal with
  | [ H' : find_comp _ _ _ _ _ = _ |- _ ]
      => run_opt ni_branch_prune ltac:(idtac; find_comp_eq H H'; rewrite H' in H)
                                 ltac:(idtac; fail 0)
  | [ |- _ ]
    => let find_comp_expr :=
      match type of H with
      | context[match find_comp ?a ?b ?c ?d ?e with | Some _ => _ | None => _ end ]
        => (constr:(find_comp a b c d e))
      end in
  let Heq := fresh "Heq" in
  let Heq' := fresh "Heq'" in
  destruct find_comp_expr as [? | ?]_eqn:Heq; try rewrite Heq;
  [ pose proof (find_comp_suc_match _ _ _ _ _ _ Heq) as Heq'; destruct Heq'
  | pose proof (find_comp_fail _ _ _ _ _ Heq);
    pose proof (find_comp_fail_prop _ _ _ _ _ Heq) ]
  end.

(*Ltac destruct_find_comp' H1 H2 :=
  let find_comp_expr :=
      match type of H with
      | context[match find_comp ?a ?b ?c ?d ?e with | Some _ => _ | None => _ end ]
        => (constr:(find_comp a b c d e))
      end in
  let Heq := fresh "Heq" in
  let Heq' := fresh "Heq'" in
  destruct find_comp_expr as [? | ?]_eqn:Heq; try rewrite Heq;
  [ pose proof (find_comp_suc_match _ _ _ _ _ _ Heq) as Heq'; destruct Heq'
  | pose proof (find_comp_fail _ _ _ _ _ Heq);
    pose proof (find_comp_fail_prop _ _ _ _ _ Heq) ].*)

Ltac destruct_comp_pf :=
  match goal with
  | [ cpf : sigT (fun _ : Reflex.comp _ _ => _ = _ ) |- _ ]
    => destruct cpf; destruct_comp
  end.

Ltac find_comp_tr_solve :=
  repeat destruct_comp_pf; try discriminate;
  unfold Reflex.match_comp, Reflex.match_comp_pf in *; simpl in *;
  destruct_atom_eqs; try discriminate; try congruence.

(*  match type of Hs1 with
  | context[match find_comp _ _ _ _ (Reflex.kcs _ _ _ _ ?s1) with | Some _ => _ | None => _ end]
    => match type of Hs2 with
       | context[match find_comp _ _ _ _ (Reflex.kcs _ _ _ _ ?s2) with | Some _ => _ | None => _ end]
         => unfold eval_hdlr_comp_pat, eval_hdlr_payload_oexpr, eval_payload_oexpr in Hs1, Hs2;
            match type of Hs1 with
            | context[match ?e1 with | Some _ => _ | None => _ end]
              => match type of Hs2 with
                 | context[match ?e2 with | Some _ => _ | None => _ end]
                   => simpl e1 in Hs1; simpl e2 in Hs2;
                      match goal with
                      | [ _ : high_out_eq _ _ _ _ _ _ ?comp_lblr |- _ ]
                        => erewrite hout_eq_find_eq with
                             (s':=s2) (clblr:=comp_lblr) in Hs1; eauto
                      end;
                      match goal with
                      | [ |- high_comp_pat _ _ _ _ _ ]
                        => clear Hs1 Hs2;
                           (*We have to clear these hypothesis for this goal so that
                             we can run simpl in * without worrying about performance
                             consequences.*)
                           solve [unfold high_comp_pat, Reflex.match_comp, match_comp_pf; intros;
                                  destruct_comp; try discriminate; simpl in *;
                                  destruct_atom_eqs;
                                  intuition; try discriminate; try congruence]
                      | [ |- high_out_eq _ _ _ _ _ _ _ /\ vars_eq _ _ _ _ _ _ _ ]
                        => idtac
                      | [ |- high_out_eq _ _ _ _ _ _ _ ]
                        => idtac
                      | [ |- vars_eq _ _ _ _ _ _ _ ]
                        => idtac
                      | [ |- ?G ]
                          => idtac "Unexpected goal" G; fail
                      end
                 end
            end
       end
  end.*)

Ltac vars_eq_tac :=
  match goal with
  | [ Hvars :  vars_eq _ _ _ _ _ _ _ |- _ ]
    => solve [ unfold vars_eq; simpl; auto
      | unfold vars_eq; simpl; inversion Hvars; auto ]
  end.

Ltac rewrite_ind_hyps :=
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
                   end; try contradiction
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
  try rewrite_ind_hyps;
  destruct_atom_eqs; try discriminate;
  repeat match goal with
  | [ H1 : context [ find_comp _ _ _ _ _ ],
      H2 : context [ find_comp _ _ _ _ _ ] |- _ ]
    => find_comp_eq H1 H2;
       rewrite H1 in H2; inversion H2
  | [ H1 : context [ find_comp _ _ _ _ _ ],
      H2 : context [ find_comp _ _ _ _ _ ] |- _ ]
    => rewrite H1 in H2; inversion H2
  end;
  try solve[
          auto; try impossible
        | intuition; try congruence
        | tac
        | destruct_cond; tac
        | find_comp_tr_solve; tac
        | repeat destruct_comp_st_vars; tac ]
  (*destruct_comp_st_vars is expensive, so try it only as
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

Ltac simpl_proj H :=
  repeat match type of H with
         | context [projT1 ?e ] => simpl (projT1 e) in H
         | context [projT2 ?e ] => simpl (projT2 e) in H
         end.

Ltac unfold_init_eval_functions H :=
  unfold initial_init_state,
  eval_base_payload_expr, eval_payload_expr,
  eval_payload_expr', shvec_replace_cast,
  shvec_replace_ith, eval_base_comp_pat,
  eval_base_payload_oexpr, eval_payload_oexpr
  in H.

Ltac unfold_hdlr_eval_functions H :=
  unfold default_hdlr_state, mk_inter_ve_st,
  eval_hdlr_payload_expr, mvar,
  eval_payload_expr, eval_payload_expr',
  shvec_replace_cast, shvec_replace_ith,
  eval_hdlr_comp_pat, eval_hdlr_payload_oexpr,
  eval_payload_oexpr in H.

Ltac simpl_nested_isrp H :=
  match type of H with
  | _ = init_state_run_cmd _ _ _ _ _ _
          (init_state_run_cmd _ _ _ _ _ _ _ _ _) _ _ =>
    unfold init_state_run_cmd at 2 in H;
    unfold_init_eval_functions H;
    match type of H with
    | _ = init_state_run_cmd _ _ _ _ _ _ ?s _ _ =>
      simpl s in H
    end
  end.

Ltac simpl_nested_hsrp H :=
  match type of H with
  | context [ hdlr_kst _ _ _ _ _
               (hdlr_state_run_cmd _ _ _ _ _ _ _ _
                (hdlr_state_run_cmd _ _ _ _ _ _ _ _ _ _ _) _ _ ) ] =>
    unfold hdlr_state_run_cmd at 2 in H;
    unfold_hdlr_eval_functions H;
    match type of H with
    | context [ hdlr_kst _ _ _ _ _
                 (hdlr_state_run_cmd _ _ _ _ _ _ _ _
                   ?s _ _ ) ] =>
      simpl s in H
    end
  | _ = hdlr_state_run_cmd _ _ _ _ _ _ _ _
          (hdlr_state_run_cmd _ _ _ _ _ _ _ _ _ _ _) _ _ =>
    unfold hdlr_state_run_cmd at 2 in H;
    unfold_hdlr_eval_functions H;
    match type of H with
    | _ = hdlr_state_run_cmd _ _ _ _ _ _ _ _
                   ?s _ _  =>
      simpl s in H
    end
  end.

Ltac simpl_step_isrp_opt H :=
  repeat first
    [ rewrite seq_rew_init in H;
      match type of H with
      | context [ init_state_run_cmd _ _ _ _ _ _
          (init_state_run_cmd ?a ?b ?c ?d ?e ?f ?g ?h ?j) _ _ ]
        => let isrp := fresh "isrp" in
           remember (init_state_run_cmd a b c d e f g h j) as isrp;
           match goal with
           | [ Heq : isrp = _ |- _ ]
             => simpl_step_isrp_opt Heq; subst isrp
           end
      end
    | rewrite ite_rew_init in H;
      match type of H with
      | context [ if num_eq ?e1 ?e2 then _ else _ ]
        => simpl (num_eq e1 e2) in H;
           match type of H with
           | context [ if num_eq ?e1 ?e2 then _ else _ ]
             => destruct (num_eq e1 e2);
                match type of H with
                | context [ init_state_run_cmd ?a ?b ?c ?d ?e ?f ?g ?h ?j ]
                  => let isrp := fresh "isrp" in
                     remember (init_state_run_cmd a b c d e f g h j) as hsrp;
                     match goal with
                     | [ Heq : isrp = _ |- _ ]
                       => simpl_step_isrp_opt Heq; subst isrp
                     end
                end
           end
      end
    | rewrite complkup_rew_init in H;
      match type of H with
      | context[ match find_comp _ _ _ _ _ with | Some _ => _ | None => _ end ]
        => unfold eval_base_comp_pat, eval_base_payload_oexpr,
           eval_payload_oexpr in H;
           match type of H with
           | context[ match find_comp ?a ?b ?c ?d ?e with | Some _ => _ | None => _ end ]
             => simpl (find_comp a b c d e) in H;
                destruct_find_comp' H;
                match type of H with
                | context [ init_state_run_cmd ?a ?b ?c ?d ?e ?f ?g ?h ?j ]
                  => let isrp := fresh "isrp" in
                     remember (init_state_run_cmd a b c d e f g h j) as hsrp;
                     match goal with
                     | [ Heq : isrp = _ |- _ ]
                       => simpl_step_isrp_opt Heq; subst isrp
                     end
                end
           end
      end
    | progress (unfold init_state_run_cmd in H;
                unfold_init_eval_functions H;
                simpl in H)
    ].

Ltac simpl_step_isrp_no_opt H :=
  simpl in H; repeat destruct_find_comp' H;
  repeat destruct_cond' H; simpl in H.

Ltac simpl_step_isrp_run_opt H :=
  run_opt rewrite_symb ltac:(idtac; simpl_step_isrp_opt H)
                       ltac:(idtac; simpl_step_isrp_no_opt H).

Ltac simpl_step_hsrp_opt H :=
  repeat first
    [ rewrite seq_rew in H;
      match type of H with
      | context [ hdlr_state_run_cmd _ _ _ _ _ _ _ _
          (hdlr_state_run_cmd ?a ?b ?c ?d ?e ?f ?g ?h ?j ?k ?i) _ _ ]
        => let hsrp := fresh "hsrp" in
           remember (hdlr_state_run_cmd a b c d e f g h j k i) as hsrp;
           match goal with
           | [ Heq : hsrp = _ |- _ ]
             => simpl_step_hsrp_opt Heq; subst hsrp
           end
      end
    | rewrite ite_rew_hdlr in H;
      match type of H with
      | context [ if num_eq ?e1 ?e2 then _ else _ ]
        => simpl (num_eq e1 e2) in H;
           match type of H with
           | context [ if num_eq ?e1 ?e2 then _ else _ ]
             => destruct (num_eq e1 e2);
                match type of H with
                | context [ hdlr_state_run_cmd ?a ?b ?c ?d ?e ?f ?g ?h ?j ?k ?i ]
                  => let hsrp := fresh "hsrp" in
                     remember (hdlr_state_run_cmd a b c d e f g h j k i) as hsrp;
                     match goal with
                     | [ Heq : hsrp = _ |- _ ]
                       => simpl_step_hsrp_opt Heq; subst hsrp
                     end
                end
           end
      end
    | rewrite complkup_rew_hdlr in H;
      match type of H with
      | context[ match find_comp _ _ _ _ _ with | Some _ => _ | None => _ end ]
        => unfold eval_hdlr_comp_pat, eval_hdlr_payload_oexpr,
           eval_payload_oexpr in H;
           match type of H with
           | context[ match find_comp ?a ?b ?c ?d ?e with | Some _ => _ | None => _ end ]
             => simpl (find_comp a b c d e) in H;
                destruct_find_comp' H;
                match type of H with
                | context [ hdlr_state_run_cmd ?a ?b ?c ?d ?e ?f ?g ?h ?j ?k ?i ]
                  => let hsrp := fresh "hsrp" in
                     remember (hdlr_state_run_cmd a b c d e f g h j k i) as hsrp;
                     match goal with
                     | [ Heq : hsrp = _ |- _ ]
                       => simpl_step_hsrp_opt Heq; subst hsrp
                     end
                end
           end
      end
    | progress (unfold hdlr_state_run_cmd in H;
                unfold_hdlr_eval_functions H;
                simpl in H)
    ].

Ltac simpl_step_hsrp_no_opt H :=
  simpl in H; repeat destruct_find_comp' H;
  repeat destruct_cond' H; simpl in H.

Ltac simpl_step_hsrp_run_opt H :=
  run_opt rewrite_symb ltac:(idtac; simpl_step_hsrp_opt H)
                       ltac:(idtac; simpl_step_hsrp_no_opt H).

Ltac symb_exec_low Hs :=
  unfold kstate_run_prog in Hs;
  simpl_proj Hs;
  simpl_step_hsrp_run_opt Hs.

Ltac solve_low_step Hlow :=
  idtac;
  match goal with
  | [ |- high_out_eq _ _ _ _ _ _ _ ]
    => ho_eq_tac ho_eq_solve_low Hlow
  | [ |- vars_eq _ _ _ _ _ _ _ ]
    => auto
  | [ |- cs_eq _ _ _ _ _ _ _ ]
    => unfold cs_eq; simpl; auto
  | _ => idtac
  end.

Ltac low_step :=
  unfold low_ok; intros;
  match goal with
  | [ Hve : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ ?s _,
      Hlow : _ = false |- _ ]
    => destruct_msg; destruct_comp;
       try discriminate;
       run_opt prune_ni ltac:(idtac; try solve [eapply prune_nop_1; eauto])
                        ltac:(idtac);
       destruct Hve; repeat subst_inter_st;
       match goal with
       |- context [ high_out_eq _ _ _ _ _ ?s _ ]
         => let ksrp := fresh "ksrp" in
            remember s as ksrp;
            match goal with
            | [ Heq : ksrp = s,
                hdlrs : sigT (fun _ :vcdesc _ => hdlr_prog _ _ _ _ _ _ _) |- _ ]
              => run_opt rewrite_symb
                         ltac:(idtac; simpl in hdlrs;
                               unfold seq, spawn, stupd, call, ite, send, complkup in hdlrs;
                               unfold hdlrs in Heq)
                         ltac:(idtac);
                 symb_exec_low Heq;                  
                 subst ksrp
            end
       end;
       simpl; repeat split;
       run_opt abstract_pf ltac:(idtac; abstract solve_low_step Hlow)
                           ltac:(idtac; solve_low_step Hlow)
  end.

Ltac ho_eq_solve_high := auto.
(*  repeat match goal with
         | [ |- _::_ = _::_ ] => f_equal; auto
         | _ => solve [auto]
         end.*)

Ltac cs_eq_solve_high :=
  repeat match goal with
         | [ |- _::_ = _::_ ] => f_equal; auto
         | _ => solve [auto]
         end.

Ltac symb_exec_high Hs1 Hs2 :=
  unfold kstate_run_prog in Hs1, Hs2;
  simpl_proj Hs1; simpl_proj Hs2;
  simpl_step_hsrp_run_opt Hs1;
  simpl_step_hsrp_run_opt Hs2.
(*          repeat match goal with
          | [ H1 : context [ find_comp _ _ _ _ _ ],
              H2 : context [ find_comp _ _ _ _ _ ] |- _ ]
            => find_comp_eq H1 H2;
               rewrite H1 in H2; inversion H2
          end).*)

Ltac solve_high_step Hhigh :=
  idtac;
  match goal with
  | [ |- high_out_eq _ _ _ _ _ _ _ ]
    => ho_eq_tac ho_eq_solve_high Hhigh
  | [ |- vars_eq _ _ _ _ _ _ _ ]
    => vars_eq_tac
  | [ |- cs_eq _ _ _ _ _ _ _ ]
    => unfold cs_eq in *; simpl; cs_eq_solve_high
  | _ => idtac
  end.

Ltac high_step :=
  unfold high_ok; intros;
  match goal with
  | [ Hve1 : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ ?s1 _,
      Hve2 : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ ?s2 _,
      Hhigh : _ = true |- _ ]
    => destruct_msg; destruct_comp;
       try discriminate;
       run_opt prune_ni ltac:(idtac; try solve [eapply prune_nop_2; eauto])
                        ltac:(idtac);
       destruct Hve1; destruct Hve2;
       repeat subst_inter_st;
       match goal with
       |- context [ high_out_eq _ _ _ _ ?s1 ?s2 _ ]
         => let ksrp1 := fresh "ksrp" in
            let ksrp2 := fresh "ksrp" in
            remember s1 as ksrp1;
            remember s2 as ksrp2;
            match goal with
            | [ Heq1 : ksrp1 = s1, Heq2 : ksrp2 = s2,
                hdlrs1 : sigT (fun _ :vcdesc _ => hdlr_prog _ _ _ _ _ _ _),
                hdlrs2 : sigT (fun _ :vcdesc _ => hdlr_prog _ _ _ _ _ _ _) |- _ ]
              => run_opt rewrite_symb
                         ltac:(idtac; simpl in hdlrs1; simpl in hdlrs2;
                               unfold seq, spawn, stupd, call, ite, send, complkup in hdlrs1;
                               unfold seq, spawn, stupd, call, ite, send, complkup in hdlrs2;
                               unfold hdlrs1 in Heq1, Heq2;
                               unfold hdlrs2 in Heq1, Heq2)
                         ltac:(idtac);
                 symb_exec_high Heq1 Heq2;                  
                 subst ksrp1; subst ksrp2
            end
       end;
       simpl; repeat split;
       run_opt abstract_pf ltac:(idtac; abstract solve_high_step Hhigh)
                           ltac:(idtac; solve_high_step Hhigh)
  end.

Ltac ni :=
  intros; apply ni_suf; [low_step | high_step].

(*Policy language tactics*)

Ltac symb_exec Hs :=
  unfold kstate_run_prog in Hs;
  simpl_proj Hs;
  simpl_step_hsrp_run_opt Hs.
(*  unfold kstate_run_prog in Hs;
  repeat match type of Hs with
         | context [projT1 ?e ] => simpl (projT1 e) in Hs
         | context [projT2 ?e ] => simpl (projT2 e) in Hs
         end;
  repeat first
         [ progress match type of Hs with
           | context [ hdlr_kst _ _ _ _ _
                         (hdlr_state_run_cmd _ _ _ _ _ _ _ _
                            (hdlr_state_run_cmd _ _ _ _ _ _ _ _ _ _ _) _ _ ) ] =>
             unfold hdlr_state_run_cmd at 2 in Hs;
             unfold default_hdlr_state, mk_inter_ve_st,
             eval_hdlr_payload_expr, mvar,
             eval_payload_expr, eval_payload_expr',
             shvec_replace_cast, shvec_replace_ith in Hs;
             match type of Hs with
             | context [ hdlr_kst _ _ _ _ _
                         (hdlr_state_run_cmd _ _ _ _ _ _ _ _
                            ?s _ _ ) ] =>
               simpl s in Hs
             end
           end
         | erewrite seq_rew in Hs; eauto
         | match type of Hs with
           | context [ if num_eq ?e1 ?e2 then _ else _ ]
             => destruct (num_eq e1 e2)
           end
         | destruct_find_comp' Hs
         | progress simpl in Hs
         ].*)

(*Ltac symb_exec H prog :=
  unfold kstate_run_prog, init_state_run_cmd, shvec_replace_cast, shvec_replace_ith,
    initial_init_state, eval_base_payload_expr, eval_payload_expr,
    eval_payload_expr', eval_base_expr, eval_expr, eval_base_term in *;
  unfold prog in *; simpl in *;
  repeat destruct_find_comp' H; repeat destruct_cond' H; simpl in *.*)

Ltac destruct_ite_pol :=
  match goal with
  |- context[ ite _ _ _ ]
    => unfold kstate_run_prog in *;
       unfold hdlr_state_run_cmd in *; simpl in *;
       repeat destruct_cond
  end.

Ltac prune_finish :=
  eauto; simpl; intuition.

Ltac unpack prune_init prune_hdlr :=
  intros;
  match goal with
  | [ H : Reflex.InitialState _ _ _ _ _ _ _ ?input _ |- _ ]
    => run_opt prune_pol ltac:(idtac; try solve [prune_init])
                         ltac:(idtac);
       destruct H;
       match goal with
       | [ Hs : ?s' = init_state_run_cmd _ _ _ _ _ _ _ ?prog _,
           Htr : Reflex.ktr _ _ _ _ _ = _ |- _ ]
         => simpl in Htr; destruct_input input;
            run_opt rewrite_symb
                    ltac:(idtac; unfold prog, seq, spawn, stupd, call, ite, send, complkup in Hs)
                    ltac:(idtac);
            simpl_step_isrp_run_opt Hs; subst s'; simpl in *
       end
  | [ H : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ _ |- _ ]
    => destruct_msg; destruct_comp;
       run_opt prune_pol ltac:(idtac; try solve [prune_hdlr]) ltac:(idtac);
       destruct H;
       match goal with
       | [ _ : ?s' = mk_inter_ve_st _ _ _ _ _ _ _ _,
           hdlrs : sigT (fun _ :vcdesc _ => hdlr_prog _ _ _ _ _ _ _) |- _ ]
         => subst s';
            match goal with
            | [ Htr : Reflex.ktr _ _ _ _
                        (kstate_run_prog _ _ _ _ _ _ _ _ _ _ _) = inhabits ?tr |- _ ]
              => let ksrp := fresh "ksrp" in
                 match type of Htr with
                 | Reflex.ktr _ _ _ _ ?s = inhabits _
                   => remember s as ksrp;
                   match goal with
                   | [ Hksrp : ksrp = s |- _ ]
                      => run_opt rewrite_symb
                                 ltac:(idtac; simpl in hdlrs;
                                       unfold seq, spawn, stupd, call, ite, send, complkup in hdlrs;
                                       unfold hdlrs in Hksrp)
                                 ltac:(idtac);
                         symb_exec Hksrp; subst ksrp;
                         simpl in *
                   end
                 end
            end
       end
  | [ H : Reflex.BogusExchange _ _ _ _ _ _ _ ?s |- _ ]
    => inversion H; subst s; clear H; simpl in *
  end; try uninhabit.
(*Ltac unpack :=
  intros;
  match goal with
  | [ H : Reflex.InitialState _ _ _ _ _ _ _ ?input ?s |- _ ]
    => (*try solve [eapply no_enablee_init; eauto; simpl; intuition];*)
       inversion H;
       match goal with
       | [ Hs : ?s' = init_state_run_cmd _ _ _ _ _ _ _ ?prog _,
           Htr : Reflex.ktr _ _ _ _ _ = _ |- _ ]
         => clear H; subst s; simpl in Htr; destruct_input input;
            match goal with
            | [ _ : context [ s' ], _ : context [ s' ], _ : context [ s' ] |- _ ]
                => symb_exec Hs prog; subst s'; simpl in *
            | _ => subst s'; symb_exec Htr prog
            end
       end
  | [ H : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ ?s |- _ ]
    => destruct_msg; destruct_comp;
       (*try solve [eapply no_enablee_hdlr; eauto; simpl; intuition];*)
       inversion H;
       match goal with
       | [ _ : ?s' = mk_inter_ve_st _ _ _ _ _ _ _ _,
           Htr : Reflex.ktr _ _ _ _ s = _,
           Hs : kstate_run_prog _ _ _ _ _ _ _ (projT1 ?hdlrs) _ _ _ = s |- _ ]
         => clear H; subst s';
            match goal with
            | [ _ : context [ s ], _ : context [ s ], _ : context [ s ] |- _ ]
                => symb_exec Hs hdlrs; subst s; simpl in *
            | _ => subst s; symb_exec Htr hdlrs
            end
       end
  | [ H : Reflex.BogusExchange _ _ _ _ _ _ _ ?s |- _ ]
    => inversion H; subst s; clear H; simpl in *
  end; try uninhabit.*)

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
         | [ H : List.In _ _ |- _ ]
           => revert H
         | [ H : forall _ : Reflex.comp _ _,
                   List.In _ _ -> _ |- _ ]
             => (*find_comp_fail*) revert H
         | _
           => idtac
         end; clear; intros;
  repeat match goal with
         | [ H : find_comp _ _ _ _ _ = _ |- _ ]
             => clear H
         end.

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
  | match_comp _ _ _ _ _ => apply decide_match_comp
  | match_comp' _ _ _ _ _ => apply decide_match_comp'
  | comp_list_match _ _ _ _ _ => apply decide_list_match_comp
  | listMatch _ _ _ => apply decide_list_match
  | msgMatch _ _ _ => apply decide_msg_match
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
  repeat
    match goal with
    | [ |- exists past : Reflex.KAction _ _ _, (?act = _ \/ ?disj_R ) /\ ?conj_R ] =>
      solve [exists act; unfold msgMatch, msgMatch'; simpl; intuition; congruence]
            || apply cut_exists
    end.

Ltac use_IH_releases :=
  match goal with
  | [ IHReach : context[ exists past : Reflex.KAction _ _ _, _ ] |- _ ]
    => repeat apply cut_exists; eapply IHReach; eauto
  end.

Ltac reach_induction prune_init prune_hdlr :=
  intros;
  match goal with
  | [ _ : Reflex.ktr _ _ _ _ _ = inhabits ?tr, H : Reflex.Reach _ _ _ _ _ _ _ _ ?s |- _ ]
      => generalize dependent tr; induction H; unpack prune_init prune_hdlr
         (*Do not put simpl anywhere in here. It breaks destruct_unpack.*)
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

Ltac invert_comp_eqs :=
  repeat match goal with
  | [ H : ?c1 = ?c2 \/ _ |- _ ]
      => match type of c1 with
         | Reflex.comp _ _ =>
           decompose [or] H; clear H;
           repeat match goal with
                  | [ Heq : ?c1 = ?c2 |- _ ]
                      => match type of c1 with
                         | Reflex.comp _ _ =>
                           compute in Heq;
                           apply comp_inv in Heq
                         end
                  end
         end
  end.

Ltac solve_exists_past :=
  invert_comp_eqs;
  try solve [ impossible
            | use_IH_releases
            | releaser_match
            | auto].

Ltac exists_past :=
  extract_match_facts;
  (*There may be conditions on s' (the intermediate state). We want
    to use these conditions to derive conditions on s.*)
  (*subst_states;*)
  (*Try to match stuff at head of trace.*)
  releaser_match;
  (*This may not clear the old induction hypothesis. Does it matter?*)
  clear_useless_hyps;
  try match goal with
      | [ cs : List.list (Reflex.comp _ _) |- _ ]
        => subst cs
      end;
  (*Should this take s as an argument?*)
  reach_induction idtac idtac;
  run_opt abstract_pf_deep ltac:(idtac; abstract solve_exists_past)
                           ltac:(idtac; solve_exists_past).

Ltac match_releases :=
  match goal with
  | [ |- Enables _ _ _ _ _ _ nil ] => constructor
  (* Induction hypothesis.*)
  | [ H : Reflex.ktr _ _ _ _ ?s = inhabits ?tr,
      IH : forall tr',
             Reflex.ktr _ _ _ _ ?s = inhabits tr' ->
             Enables _ _ _ _ ?past ?future tr'
      |- Enables _ _ _ _ ?past ?future ?tr ] =>
    auto
  (*Branch on whether the head of the trace matches.*)
  | [ |- Enables ?pdv ?compt ?comps ?comptdec _ ?future (?act::_) ] =>
    let H := fresh "H" in
    let A := fresh "A" in
    pose proof (decide_act pdv compt comps comptdec future act) as H;
    destruct H as [A|A]; simpl in A; repeat autounfold in A; simpl in A;
    [ tauto ||
      (decompose [and] A; apply E_future;
       [ match_releases | try solve [exists_past] ])
    | tauto ||
      (destruct_neg_conjuncts A; apply E_not_future;
       [ match_releases | assumption ]) ]
  (* In some cases, one branch is impossible, so contradiction
     solves the goal immediately.
     In other cases, there are variables in the message payloads,
     so both branches are possible.
   *)
  end.

Ltac use_IH_disables :=
  match goal with
  | [ IHReach : context[forall tr' : Reflex.KTrace _ _ _, _],
      _ : Reflex.ktr _ _ _ _ ?s = inhabits ?tr |- _ ]
      => eapply IHReach; eauto (*TODO: auto may not always work here.*)
  end.

Ltac specialize_comp_hyps :=
  match goal with
  |- context[ ActionMatch.match_comp' _ _ _ _ ?c ]
    => repeat match goal with
              | [ H : forall c' : Reflex.comp _ _, _ |- _ ]
                => specialize (H c); simpl in H
              end
  end.

Ltac decompose_not_match :=
  match goal with
  |- _ -> _
    => let H := fresh "H" in
       intro H; try decompose [and] H
  end.

Ltac rewrite_st_eqs :=
  match goal with
  | [ H : _ = fst (kst _ _ _ _ _) |- _ ]
      => rewrite <- H in *
  | [ H : _ = fst (snd (kst _ _ _ _ _)) |- _ ]
      => rewrite <- H in *
  | [ H : _ = fst (snd (snd (kst _ _ _ _ _))) |- _ ]
      => rewrite <- H in *
  | [ H : _ = fst (snd (snd (snd (kst _ _ _ _ _)))) |- _ ]
      => rewrite <- H in *
  | [ H : _ = fst (snd (snd (snd (snd (kst _ _ _ _ _))))) |- _ ]
      => rewrite <- H in *
  | [ H : fst (kst _ _ _ _ _) = _ |- _ ]
      => rewrite <- H in *
  | [ H : fst (snd (kst _ _ _ _ _)) = _ |- _ ]
      => rewrite <- H in *
  | [ H : fst (snd (snd (kst _ _ _ _ _))) = _ |- _ ]
      => rewrite <- H in *
  | [ H : fst (snd (snd (snd (kst _ _ _ _ _)))) = _ |- _ ]
      => rewrite <- H in *
  | [ H : fst (snd (snd (snd (snd (kst _ _ _ _ _))))) = _ |- _ ]
      => rewrite <- H in *
  end.

Ltac no_disabler_init_tac disabler :=
  match goal with
  | [ _ : InitialState ?payd ?compt ?comptdec ?comps ?kstd ?ienvd ?init ?i ?s,
      _ : Reflex.ktr _ _ _ _ ?s = inhabits ?trs |- _ ]
    => apply (no_disabler_init payd compt comptdec comps ienvd kstd init i
                               disabler s)
       with (tr:=trs); auto; simpl; intuition; fail
end.

Ltac no_disabler_hdlr_tac disabler :=
  match goal with
  | [ _ : @Reflex.ValidExchange ?nb_msg ?payd ?compt ?comptdec ?comps ?kstd ?handlers ?cc ?mm ?i ?s ?s',
      _ : Reflex.ktr _ _ _ _ ?s' = inhabits ?tr' |- _ ]
    => apply (no_disabler_hdlr payd compt comptdec comps kstd handlers cc mm i
         disabler s s') with (tr:=tr');
       auto;
       match goal with
       | [ |- no_match _ _ _ _ _ _ _ ]
         => simpl; intuition; fail 1
       | [ IHReach : context[forall tr' : Reflex.KTrace _ _ _, _] |- _ ]
         => apply IHReach; auto;
            match goal with
            | [ |- List.In _ (Reflex.kcs _ _ _ _ _) ]
                => solve [apply (no_spawn_cs nb_msg payd compt comptdec comps
                                      kstd handlers s s' cc mm i); simpl; auto]
            | [ |- context [ Reflex.kst _ _ _ _ _ ] ]
                => solve [rewrite <- (no_stupd_kst nb_msg payd compt comptdec comps kstd handlers
                                         s s' cc mm i); simpl; auto]
            | [ |- context [ Reflex.kcs _ _ _ _ _ ] ]
                => solve [apply (comp_in_prop nb_msg payd compt
                                       comptdec comps kstd handlers s s' _ cc mm i);
                   auto]
            end
       end
  end.

Ltac solve_forall_not_disabler n act disabler cont :=
  match goal with
  | [ H :  context[ List.In ?act _ ] |- _ ]
      => simpl in *; decompose [or] H; try subst;
         try specialize_comp_hyps; autounfold; simpl;
         try solve [try decompose_not_match; try rewrite_st_eqs;
                    try solve [ impossible
                              | tauto
                              | use_IH_disables
                              | intuition; try congruence]
                   | match n with
                     | O => fail
                     | S ?n' =>
                       match goal with
                       | [ Hact' : List.In act _ |- _ ]
                           => cont n' act Hact' disabler
                       end
                     end
                   ]
  end.

(*This function should be passed a state. It will then attempt to prove
  that there are no instances of the disabler (should it be passed the disabler?)
  anywhere in the trace of that state.*)
(*There are two situations:
1.) The trace of the state is fully concrete: no induction required.
2.) The trace is not fully concrete: induction required.*)
Ltac forall_not_disabler n act Hact disabler :=
(*  destruct_action_matches;*)
  try solve [impossible];
  extract_match_facts;
  simpl in Hact; decompose [or] Hact;
  try (subst act; solve [auto | tauto | intuition]);
  try contradiction;
(*   (*There may be conditions on s' (the intermediate state). We want
    to use these conditions to derive conditions on s.*)
  subst_states;*)
  (*This may not clear the old induction hypothesis. Does it matter?*)
  clear_useless_hyps;
  try match goal with
      | [ cs : List.list (Reflex.comp _ _) |- _ ]
        => match goal with
           | [ H : List.In _ cs |- _ ]
             => clear H
           end
      end;
  try match goal with
      | [ H : List.In _ (Reflex.kcs _ _ _ _ _) |- _ ]
          => clear H
      end;
  (*Should this take s as an argument?*)
  let prune_init := try solve [no_disabler_init_tac disabler] in
  let prune_hdlr := try solve [no_disabler_hdlr_tac disabler] in
  reach_induction prune_init prune_hdlr;
  run_opt abstract_pf_deep ltac:(idtac; abstract (solve_forall_not_disabler n act disabler forall_not_disabler))
                           ltac:(idtac; solve_forall_not_disabler n act disabler forall_not_disabler).
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

Ltac match_disables disabler :=
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
           (decompose [and] A; apply D_disablee;
            [ match_disables disabler
             | let act := fresh "act" in
               let Hact := fresh "Hact" in
               intros act Hact; try forall_not_disabler 3 act Hact disabler ])
         | tauto ||
           (destruct_neg_conjuncts A; apply D_not_disablee;
            [ match_disables disabler | assumption ]) ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  end.
(*  match goal with
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
  end.*)

Ltac act_match :=
  simpl in *; autounfold; simpl;
  repeat destruct_comp_st_vars; intuition.

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

Ltac crush_with_lem lem_init lem_hdlr match_policy :=
  let prune_init := solve [ eapply lem_init; prune_finish ] in
  let prune_hdlr := solve [ eapply lem_hdlr; prune_finish ] in
  reach_induction prune_init prune_hdlr;
  run_opt abstract_pf ltac:(idtac; try abstract match_policy)
                      ltac:(idtac; try match_policy).

Ltac crush :=
  intros;
  match goal with
  | [ |- context [ ImmBefore _ _ _ _ _ _ _ ] ]
    => crush_with_lem (@no_after_IB_init) (@no_after_IB_hdlr) ltac:(idtac; match_immbefore)
  | [ |- context [ ImmAfter _ _ _ _ _ _ _ ] ]
    => crush_with_lem (@no_before_IA_init) (@no_before_IA_hdlr) ltac:(idtac; match_immafter)
  | [ |- context [ Enables _ _ _ _ _ _ _ ] ]
    => crush_with_lem (@no_enablee_init) (@no_enablee_hdlr) ltac:(idtac; match_releases)
  | [ |- context [ Disables _ _ _ _ ?disabler _ _ ] ]
    => crush_with_lem (@no_disablee_init) (@no_disablee_hdlr) ltac:(idtac; match_disables disabler)
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
