Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexHVec.
Require Import ReflexIO.
Require Import NIExists.
Require Import Ynot.
Require Import PruneFacts.

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
  Definition sendall := SendAll PAYD COMPT COMPS KSTD.
  Definition spawn := Spawn PAYD COMPT COMPS KSTD.
  Definition call := Reflex.Call PAYD COMPT COMPS KSTD.
  Definition stupd := StUpd PAYD COMPT COMPS KSTD.

  Definition stvar {cc envd m} v :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD cc m) envd (StVar _ _ _ _ _ _ _ v).
  Definition envvar {cc m} envd i :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD cc m) envd
         (Base _ _ _ _ _ _ _ (Var _ envd i)).
  Definition slit {cc envd m} v :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD cc m) envd (Base _ _ _ _ _ _ _ (SLit _ _ v)).
  Definition nlit {cc envd m} v :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD cc m) envd (Base _ _ _ _ _ _ _ (NLit _ _ v)).
  Definition ccomp {cc envd m} :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD cc m) envd (CComp _ _ _ _ _ _ _).
  Definition i_slit v := Term COMPT (base_term _) IENVD (SLit _ _ v).
  Definition i_nlit v := Term COMPT (base_term _) IENVD (NLit _ _ v).
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
    BinOp COMPT term envd
          (Eq _ d) e1 e2.

  Definition splitfst envd term c s :=
    UnOp COMPT term envd (SplitFst _ c) s.

  Definition splitsnd envd term c s :=
    UnOp COMPT term envd (SplitSnd _ c) s.

  Definition mvar
  {envd} (t : fin NB_MSG) {ct} i :=
  (Term COMPT _ _ (MVar PAYD COMPT COMPS KSTD ct t envd i)).

  Definition cconf
  {envd} {t : fin NB_MSG} ct i :=
  (Term COMPT _ _ (CConf PAYD COMPT COMPS KSTD ct t envd i)).

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
         destruct ct
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

Ltac destruct_state :=
  match goal with
  |- context[kst _ _ _ _ ?s]
    => let kvars := fresh "kvars" in
       set (kvars:=kst _ _ _ _ s);
       destruct_pay kvars;
       repeat destruct_comp_var; simpl
  end.

Ltac destruct_cond :=
match goal with
|- context[ if ?e then _ else _ ] => destruct e
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
         => rewrite Hout with (tr:=tr1) (tr':=tr2); auto;
            inversion Hvars; auto
       end
  end.

Ltac ho_eq_tac tac Hlblr :=
  unfold high_out_eq; simpl; intros;
  repeat remove_redundant_ktr;
  repeat uninhabit; simpl;
  simpl in Hlblr; try rewrite Hlblr;
  try solve[tac | destruct_cond; tac
    | state_var_branch | destruct_state; tac]
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
  | [ Hve : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ _,
      Hlow : _ = false |- _ ]
    => destruct_msg; destruct_comp; try discriminate;
       try solve [eapply prune_nop_1; eauto];
       inversion Hve; repeat subst_inter_st; simpl;
       try destruct_ite; split;
       match goal with
       | [ |- high_out_eq _ _ _ _ _ _ _ ]
         => ho_eq_tac ho_eq_solve_low Hlow
       | [ |- vars_eq _ _ _ _ _ _ _ ]
         => auto
       | _ => idtac
       end
  end.

Ltac ho_eq_solve_high :=
  repeat match goal with
         | [ |- _::_ = _::_ ] => f_equal; auto
         | _ => auto
         end.

Ltac high_steps :=
  unfold high_ok; intros;
  match goal with
  | [ Hve1 : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ _,
      Hve2 : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ _,
      Hhigh : _ = true |- _ ]
    => destruct_msg; destruct_comp; try discriminate;
       try solve [eapply prune_nop_2; eauto];
       inversion Hve1; inversion Hve2;
       repeat subst_inter_st; simpl;
       try destruct_ite; split;
       match goal with
       | [ |- high_out_eq _ _ _ _ _ _ _ ]
         => ho_eq_tac ho_eq_solve_high Hhigh
       | [ |- vars_eq _ _ _ _ _ _ _ ]
         => vars_eq_tac
       | _ => idtac
       end
  end.

Ltac ni :=
  intros; apply ni_suf; [low_step | high_steps].

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
