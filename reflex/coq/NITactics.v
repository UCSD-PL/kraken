Require Import NonInterference.
Require Import Reflex.

Require Import Ynot.

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

(*Destructs num, str, or fd equalities in the context.*)
Ltac destruct_eq H :=
  repeat match type of H with
         | context[if ?x then _ else _ ]
           => destruct x
         end.
 (* repeat match type of H with
         | context[num_eq ?a ?b]
           => destruct (num_eq a b); simpl in *
         | context[str_eq ?a ?b]
           => destruct (str_eq a b); simpl in *
         | context[fd_eq ?a ?b]
           => destruct (fd_eq a b); simpl in *
         end.*)

Ltac destruct_input input :=
  simpl in input; (*compute in input;*)
  match type of input with
  | unit => idtac
  | _ => let x := fresh "x" in
         let input' := fresh "input'" in
         destruct input as [x input']; destruct_input input'
  end.

Ltac unpack_inhabited :=
  repeat match goal with
         | [ H : ktr _ _ _ _ _ = inhabits ?tr |- _ ]
           => simpl in H; apply pack_injective in H; subst tr
         end.

Ltac destruct_comp :=
  match goal with
  | [ c : Reflex.comp _ _ |- _ ]
      => destruct c
  end.

Ltac unpack :=
  match goal with
  (*Valid exchange.*)
  | [ s : Reflex.kstate _ _ _ _, s' : Reflex.kstate _ _ _ _ |- _ ]
    => match goal with
       | [ _ : kstate_run_prog _ _ _ _ _ _ _ _ s _ = s' |- _ ]
         => subst s; subst s'
       end
  (*Initialization.*)
  | [ s : Reflex.init_state _ _ _ _ _ |- _ ]
    => match goal with
         | [ H : s = Reflex.init_state_run_cmd _ _ _ _ _ _ _ _ |- _ ]
           => subst s
       end
  (*Bogus msg*)
  end; unpack_inhabited.

Ltac spawn_call :=
      match goal with
      | [ Hcall : call_ok _ _ _ _ _ _ |- call_ok _ _ _ _ _ _ ]
          => repeat apply call_ok_sub in Hcall; try assumption;
             apply call_ok_sym in Hcall; try assumption;
             repeat apply call_ok_sub in Hcall; try assumption;
             apply call_ok_sym; try assumption
      | [ Hspawn : spawn_ok _ _ _ _ _ _ |- spawn_ok _ _ _ _ _ _ ]
          => repeat apply spawn_ok_sub in Hspawn; try assumption;
             apply spawn_ok_sym in Hspawn; try assumption;
             repeat apply spawn_ok_sub in Hspawn; try assumption;
             apply spawn_ok_sym; try assumption
      end.

Ltac high_steps :=
  intros;
  match goal with
  | [ IH : NonInterferenceSt _ _ _ _ _ _ _ _ |- _ ]
    => unfold NonInterferenceSt in *; intros;
       match goal with
       | [ Hve1 : ValidExchange _ _ _ _ _ _ _ _ _ _,
           Hve2 : ValidExchange _ _ _ _ _ _ _ _ _ _,
           Hins : inputs _ _ _ _ _ = inputs _ _ _ _ _,
           Hhigh : _ _ = true |- _ ]
         => inversion Hve1; inversion Hve2;
            destruct_msg; destruct_comp; repeat unpack;
             simpl in *; rewrite Hhigh in *; inversion Hins;
            f_equal; auto; apply IH; auto; try spawn_call
       end
  end.

Ltac low_step :=
  intros;
  match goal with
  | [ IH : NonInterferenceSt _ _ _ _ _ _ _ _ |- _ ]
    => unfold NonInterferenceSt in *; intros;
       match goal with
       | [ Hve : ValidExchange _ _ _ _ _ _ _ _ _ _,
           Hlow : _ _ = false |- _ ]
         => inversion Hve; destruct_msg; destruct_comp; repeat unpack;
            simpl in *; rewrite Hlow in *; apply IH; auto; try spawn_call
       end
  end.

Ltac ni :=
  apply ni_suf; [high_steps | low_step].