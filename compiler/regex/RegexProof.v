Require Import RegexNoInd.
Require Import Reflex.
Require Import List.
Require Import ReflexBase.
Require Import ReflexFin.
Require Import Eqdep.


Ltac decide_act :=
  match goal with
  | [ H : decide (?a0) |- decide (?a0 /\ ?a1 /\ ?a2) ]
      => destruct H; cut (decide (a1 /\ a2)); try tauto
  | [ H : decide (?a0) |- decide (?a0 /\ ?a1) ]
      => destruct H; cut (decide (a1)); try tauto
  | [ H : decide (?a) |- decide (?a) ]
      => auto
  | [ |- context[argMatch ?o ?s] ]
      => let H := fresh "H" in assert (decide (argMatch o s)) as H by
         (destruct o; simpl; (repeat decide equality) || auto)
  end.

Ltac reduceMsgMatch :=
  match goal with
  | [ |- context[fin_eq_dec ?f1 ?f2] ]
    => destruct (fin_eq_dec f1 f2)
  | [ Heq : _ = ?fin |- context[match ?Heq with | eq_refl => _ end] ]
    => destruct Heq
  end.

Definition decide_payload : forall NB_MSG PDV tag opl pl,
                              decide (@packedPLMatch NB_MSG PDV tag opl pl).
Proof.
  intros.
  unfold packedPLMatch.
  destruct (@lkup_tag NB_MSG PDV tag).
  induction x.
    auto.

    simpl.
    destruct p.
    simpl in *.
    destruct opl.
    destruct pl.
    destruct s0.
    destruct d; simpl in *;
    assert (decide (s0 = s2)) by repeat decide equality;
    decide_act; auto.
    simpl.
    cut (decide (unpackedPLMatch x s s1 s3)).
    tauto.
    auto.
Defined.

Definition decide_msg : forall NB_MSG PDV omsg msg,
                          decide (@msgMatch NB_MSG PDV omsg msg).
Proof.
  intros.
  destruct omsg.
    destruct msg.
    destruct o.
    simpl.
    unfold msgMatch'.
    reduceMsgMatch.
    simpl in *.
    reduceMsgMatch.
    apply decide_payload.
    auto.
    auto.
Defined.

Definition decide_act : forall NB_MSG PDV oact act,
                          decide (@AMatch NB_MSG PDV oact act).  
Proof.
  intros. destruct act; destruct oact; simpl in *; auto.
    repeat decide_act.

    repeat decide_act.

    repeat decide_act.

    repeat decide_act;
    apply decide_msg.

    repeat decide_act;
    apply decide_msg.

    repeat decide_act.
Defined.

Inductive RegexpProp {NB_MSG} {PDV} : Type :=
| REP_Atom   : @KOAction NB_MSG PDV -> option Prop -> RegexpProp
| REP_NAtom  : @KOAction NB_MSG PDV -> option Prop -> RegexpProp
| REP_Any    : RegexpProp
| REP_Alt    : RegexpProp -> RegexpProp -> RegexpProp
| REP_Star   : RegexpProp -> RegexpProp
| REP_Concat : RegexpProp -> RegexpProp -> RegexpProp.

Definition accepts_empty {NB_MSG} {PDV} (re:@Regexp NB_MSG PDV) : Prop :=
  match re with
  | RE_Star _ => True
  | _         => False
  end.

Fixpoint derive {NB_MSG} {PDV} re act :
  list (Prop*option (@Regexp NB_MSG PDV)) :=
  match re with
  | RE_Atom oact => (AMatch oact act, None)::nil
  | RE_NAtom oact => (~AMatch oact act, None)::nil
  | RE_Any => (True, None)::nil
  | RE_Alt r1 r2 => (derive r1 act) ++ (derive r2 act)
  | RE_Star r => map (fun (pair:(Prop*option Regexp)) =>
                        let (p, ore) := pair in
                        match ore with
                        | None => (p, Some re)
                        | Some r' => (p, Some (RE_Concat r' re))
                        end)
                     (derive r act)
  | RE_Concat r1 r2 => map (fun (pair:(Prop*option Regexp)) =>
                              let (p, ore) := pair in
                              match ore with
                                | None => (p, Some r2)
                                | Some r' => (p, Some (RE_Concat r' r2))
                              end)
                           (derive r1 act)
  end.

Fixpoint match_re {NB_MSG} {PDV} (re:@Regexp NB_MSG PDV) tr : Prop :=
  match tr with
  | nil => accepts_empty re
  | act::tr' => (*exists pair, In pair (@derive NB_MSG PDV re act)
                             /\ (fst pair /\ match snd pair with
                                             | None => tr' = nil
                                             | Some r' => match_re r' tr'
                                             end)
  end.*)
                             
 fold_left (fun p (pair:(Prop*option Regexp)) =>
                            let (p', ore) := pair in
                            match ore with
                            | None => p \/ (p' /\ tr' = nil)
                            | Some r' => p \/ (p' /\ match_re r' tr')
                            end)
                         (@derive NB_MSG PDV re act)
                         False
end.
(*
Fixpoint derive {NB_MSG} {PDV} re : RegexpProp :=
fix derive_match' tr :=
  match tr with
  | nil     => (accepts_empty NB_MSG PDV re, re)
  | act::tl => match re with
               | REP_Atom oact _ => REP_Atom oact (AMatch oact act)
               | REP_NAtom oact _ => REP_NAtom oact (~AMatch oact act)
               | REP_Any => REP_Any
               | REP_Alt r1 r2 => REP_Alt (derive_match r1 tr)
                                         (derive_match r2 tr)
               | REP_Star r => REP_Concat (derive_match r tr) re
               | REP_Concat r1 r2 =>    (derive_match r1 (act::nil)
                                        /\ derive_match r2 tl)
                                    \/ (accepts_empty _ _ r1
                                        /\ derive_match r2 (act::tl))
               end
  end.

Fixpoint match {NB_MSG} {PDV} re tr : Prop :=
  
*)