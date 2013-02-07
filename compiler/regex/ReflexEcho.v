Require Import String.

Require Import Reflex.
Require Import ReflexFin.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import Regex.
Require Import Ynot.
Require Import List.
Require Import Eqdep.

Definition NB_MSG : nat := 1.

Definition PDV : payload_desc_vec NB_MSG :=
  ( existT _ 1 (str_d, tt)
  , tt
  ).

Definition HANDLERS : @handler NB_MSG PDV :=
  (fun m =>
    match tag m as _tm return
      @sdenote _ SDenoted_payload_desc (@lkup_tag NB_MSG PDV _tm) -> _
    with
    | None => fun pl =>
      let (s, _) := pl in
         Send m (CurChan m) (MsgExpr m None (SLit m s, tt))
      :: nil
    | Some bad => fun _ =>
      match bad with end
    end (pay m)
  )
.

Definition send_star :=
  RE_Star (RE_Alt (RE_Atom (@KOSelect NB_MSG PDV None None))
                  (RE_Alt (RE_Atom (@KORecv NB_MSG PDV None None))
                          (RE_Alt (RE_Atom (@KOSend NB_MSG PDV None None))
                                  (RE_Alt (RE_Atom
                                             (@KOExec NB_MSG PDV None None None))
                                          (RE_Atom
                                             (@KOBogus NB_MSG PDV None None)))))).

Definition echo_re :=
  RE_Star
    (RE_Alt
       (RE_NAtom (@KOSend NB_MSG PDV None
                          (Some (@Build_opt_msg NB_MSG PDV
                                                None (None, tt)))))
       (RE_Concat
          (RE_Atom (@KOSend NB_MSG PDV None
                            (Some (@Build_opt_msg NB_MSG PDV
                                                  None (None, tt)))))
          (RE_Atom (@KORecv NB_MSG PDV None
                            (Some (@Build_opt_msg NB_MSG PDV
                                                  None (None, tt))))))).

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

Ltac computeMsgMatch NUM_MSG :=
  match goal with
  | [ |- context[msgMatch _ _] ]
    => unfold msgMatch; unfold msgMatch';
       simpl; computeMsgMatch NUM_MSG
  | [ |- context[match fin_eq_dec ?fin1 ?fin2 with
                 | left _ => _ | right _ => _ end] ]
    => destruct (@fin_eq_dec NUM_MSG fin1 fin2) as [ ?Heq | ?Hneq ];
       [ assert (Heq = eq_refl fin1) as ?F by apply UIP_refl;
         rewrite F; compute; intuition
       | intuition ]
  end.

Ltac printCtxt :=
  repeat (match goal with [ H: _ |- _ ] => revert H end);
  match goal with |- ?G => idtac G end.

Ltac matchAtom NUM_MSG :=
  match goal with
  | [ |- RMatch (RE_Atom _) (_::nil) ]
      => apply RM_Atom; constructor; auto; matchAtom NUM_MSG
  | [ |- RMatch (RE_NAtom _) (_::nil) ]
      => apply RM_NAtom; unfold not; inversion 1; matchAtom NUM_MSG
  | [ |- context G[msgMatch _ _ ] ]
      => computeMsgMatch NUM_MSG
  | [ H : msgMatch _ _ |- _ ]
      => revert H; computeMsgMatch NUM_MSG
  end.

Ltac matchRE NUM_MSG :=
  match goal with
  | [ |- RMatch (RE_Atom _) (_::nil) ]
      => solve [ matchAtom NUM_MSG ]
  | [ |- RMatch (RE_NAtom _) (_::nil) ]
      => solve [ matchAtom NUM_MSG ]
  | [ |- RMatch (RE_Alt _ _) _ ]
      => constructor; (left; matchRE NUM_MSG) || (right; matchRE NUM_MSG)
  | [ |- RMatch (RE_Concat _ _) (_ ++ _) ]
      => constructor; matchRE NUM_MSG
  | [ |- RMatch (RE_Star _) (_ ++ _) ]
      => constructor; matchRE NUM_MSG
  | [ |- RMatch (RE_Star _) nil ]
      => solve [constructor]

  (*If there are no matches, we may need to get the trace
    into the right form by breaking it into two lists.*)
  | [ |- RMatch _ (?tr1 ++ ?act1::?tr2) ]
      => replace (tr1 ++ act1::tr2) with
         ((tr1 ++ (act1::nil)) ++ tr2) by reflexivity;
         simpl (tr1 ++ (act1::nil)); matchRE NUM_MSG
  | [ |- RMatch _ (?act::?tl) ]
      => replace (act::tl) with
         ((act::nil) ++ tl) by reflexivity; matchRE NUM_MSG

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

Theorem always_send : forall st tr,
  Reach HANDLERS st -> inhabits tr = ktr st ->
  RMatch send_star tr.
Proof.
  intros.
  unfold send_star.
  generalize dependent tr.
  induction H; intros; simpl in *;
  try destruct_msg; unpack; matchRE NB_MSG.
Qed.

Theorem echo : forall st tr,
  Reach HANDLERS st -> inhabits tr = ktr st ->
  RMatch echo_re tr.
Proof.
  intros.
  unfold echo_re.
  generalize dependent tr.
  induction H; intros; simpl in *;
  try destruct_msg; unpack; matchRE NB_MSG.
Qed.