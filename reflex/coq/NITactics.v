Require Import NIExists.
Require Import Reflex.

Require Import Ynot.
Require Import PruneFacts.

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
      | inversion Hvars; auto ]
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
  |- context[ Ite _ _ _ _ _ _ _ _ _ ]
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