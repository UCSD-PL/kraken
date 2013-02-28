Require Import Reflex.
Require Import ReflexDenoted.
Require Import ReflexBase.
Require Import ReflexFin.
Require Import Ynot.
Require Import Regex.
Require Import Eqdep.

Ltac unpack :=
  match goal with
  | [ s : kstate, H : ?s = _ |- _ ]
      (*This is problematic because it destroys information about s*)
      => apply f_equal with (f:=ktr) in H; rewrite H in *;
         simpl in *; unpack
  | [ H: [_]%inhabited = [_]%inhabited |- _ ] =>
    apply pack_injective in H;
    rewrite -> H in * || rewrite <- H in *
  end.

Ltac printCtxt :=
  repeat (match goal with [ H: _ |- _ ] => revert H end);
  match goal with |- ?G => idtac G end.

Ltac matchAtom NUM_MSG :=
  match goal with
  | [ |- RMatch (RE_Atom _) (_::nil) ]
      => apply (@RM_Atom NUM_MSG);
         constructor; auto; (*auto takes care of simple obligations*)
         matchAtom NUM_MSG
  | [ |- RMatch (RE_NAtom _) (_::nil) ]
      => apply (@RM_NAtom NUM_MSG); unfold not;
         inversion 1; matchAtom NUM_MSG
  | [ |- context G[msgMatch _ _ ] ]
      => compute; intuition
  | [ H : msgMatch _ _ |- _ ]
      => compute in H; intuition
  end.

Ltac separateAct :=
  match goal with
  | [ |- context[RMatch _ (?tr1 ++ ?act1::?tr2)] ]
      => replace (tr1 ++ act1::tr2) with
         ((tr1 ++ (act1::nil)) ++ tr2) by reflexivity;
         simpl (tr1 ++ (act1::nil))
  | [ |- context[RMatch _ (?act::?tl)] ]
      => replace (act::tl) with
         ((act::nil) ++ tl) by reflexivity
  end.

Ltac matchRE NUM_MSG :=
  match goal with
  | [ |- RMatch (RE_Atom _) (_::nil) ]
      => solve [matchAtom NUM_MSG]
  | [ |- RMatch (RE_NAtom _) (_::nil) ]
      => solve [matchAtom NUM_MSG]
  | [ |- RMatch (RE_Alt _ _) _ ]
      => constructor; (left; matchRE NUM_MSG) || (right; matchRE NUM_MSG)
  | [ |- RMatch (RE_Concat _ _) (_ ++ _) ]
      => constructor; matchRE NUM_MSG
  | [ |- RMatch (RE_Star _) (_ ++ _) ]
      => constructor; matchRE NUM_MSG
  | [ |- RMatch (RE_Star _) nil ]
      => solve [constructor]
  | [ |- RMatch RE_Any _ ]
      => solve [constructor]

  (*If there are no matches, we may need to get the trace
    into the right form by breaking it into two lists.*)
  | _ => separateAct; matchRE NUM_MSG

  (*If all else fails, hopefully the goal follows easily from
    the context.*)
  | [ |- RMatch _ _ ]
      => solve [auto]
  end.

Ltac destruct_msg :=
  match goal with
  (*Tag is Some False*)
  | [ f : False |- _ ]
      => destruct f
  | [ pay : s[[lkup_tag _]] |- _ ]
      => destruct pay; simpl in *
  | [ tag : fin _ |- _ ]
      => destruct tag; destruct_msg
  | [ m : msg |- _ ]
      => destruct m; destruct_msg
  end.

Ltac decide_var x NUM_MSG :=
  let t := type of x in
  revert dependent x;
  match goal with
  | [ y : t |- _ ]
      => intro x; let H := fresh "H" in
         assert (decide (x = y)) as H by repeat decide equality;
         let Heq := fresh "H" in
         let Hneq := fresh "H" in
         destruct H as [Heq | Hneq];
         [ rewrite Heq in * | ];
         solve [intros; matchRE NUM_MSG]
          || (revert dependent y; decide_var x NUM_MSG)
  end.