Require Import RelationClasses.
Require Import Ynot.

Open Scope hprop_scope.
Open Scope stsepi_scope.

Ltac inv H := inversion H; subst; clear H.

Ltac sep' := sep fail idtac.

Ltac discharge_pure :=
sep';
repeat (
match goal with |- _ ==> ?r => match r with context C [ [?p] ] =>
  let c := context C[emp] in
  let t := constr:(c * [p]) in
  eapply himp_trans with (Q := t);
  [ apply himp_empty_prem'; apply himp_split;
    [ sep' | apply himp_pure' ]
  | sep'
  ]
end end
).

(*
Theorem himp_l : forall l r l', l ==> l' -> l * r ==> l' * r.
Proof. sep fail idtac. Qed.

Theorem himp_r : forall l r r', r ==> r' -> l * r ==> l * r'.
Proof. sep fail idtac. Qed.

Theorem himp_r_comm : forall l r r', r ==> r' -> l * r ==> r' * l.
Proof. sep fail idtac. Qed.

Theorem himp_l_comm : forall l r l', l ==> l' -> l * r ==> r * l'.
Proof. sep fail idtac. Qed.

Theorem himp_comm : forall l r, l * r ==> r * l.
Proof. sep fail idtac. Qed.

Theorem himp_assoc_lr : forall s a b c, s ==> (a * b) * c -> s ==> a * (b * c).
Proof. intros. eapply himp_trans. apply H. sep fail idtac. Qed.

Theorem himp_assoc_rl : forall s a b c, s ==> a * (b * c) -> s ==> (a * b) * c.
Proof. intros. eapply himp_trans. apply H. sep fail idtac. Qed.

Ltac move_l target term :=
  match term with
  | target * ?r => constr:(himp_refl term)
  | ?l * target => constr:(himp_comm l target)
  | ?l * ?r =>
    match l with context [ target ] =>
      let lres := move_l target l in
      constr:(himp_assoc_lr _ _ _ _ (himp_l l r _ lres))
    end
  | ?l * ?r =>
    match r with context [ target ] =>
      let rres := move_l target r in
      let r' := constr:(himp_r_comm l r _ rres) in
      constr:(himp_assoc_lr _ _ _ _ r')
    end
  | _ => constr:(@himp_refl term)
  end.

Ltac move_r target term :=
  match term with
  | target * ?r => constr:(himp_comm target r)
  | ?l * target => constr:(himp_refl term)
  | ?l * ?r =>
    match l with context [ target ] =>
      let mvl := move_r target l in
      let a := constr:(himp_l l r _ mvl) in
      let b := constr:(himp_comm_conc a) in
      constr:(himp_assoc_rl _ _ _ _ b)
    end
  | ?l * ?r =>
    match r with context [ target ] =>
      let rres := move_r target r in
      constr:(himp_assoc_rl _ _ _ _ (himp_r l _ _ rres))
    end
  | _ => constr:(@himp_refl term)
  end.

Parameters a b c d e f : hprop.
Parameters p q r s t u : Prop.

(*

Goal emp ==> emp.

let H := (move_r f (f * a)) in pose proof H.
let H := (move_r f (a * f)) in pose proof H.
let H := (move_r f (a * (b * f))) in pose proof H.
let H := (move_r f ((a * b) * f)) in pose proof H.
let H := (move_r f (a * (b * f) * c)) in pose proof H.
SearchAbout (?s ==> ?a * ?b -> ?s ==> ?b * ?a).
Print himp_comm_conc.
let H := (move_r f (a * (b * f * d) * c)) in pose proof H.
Set Printing All. idtac.

*)

Goal (a * (b * [p]) * c * [q]) ==> (c * d * (([r] * e) * [t])).


discharge_pure.



apply himp_split.  sep fail idtac.

  ; apply himp_split; [ apply himp_refl | ].


eapply empty_right.

Theorem rm_emp_l : forall h, h * emp ==> h.
Proof. sep fail idtac. Qed.

Ltac add_pure_hypotheses :=
repeat (
match goal with |- ?l ==> ?r => match l with context [ [?p] ] =>
  let H := fresh "H" in
  let f := move_l [p] l in
  pose proof f as H;
  eapply himp_trans; [ apply H |  ];
  apply himp_inj_prem; clear H; intro
end end
).

add_pure_hypotheses.

SearchAbout ([?p]).

match goal with |- ?l ==> ?r => match r with context [ [?p] ] =>
  let H := fresh "H" in
  let f := move_l [p] r in
  pose proof f as H
end end.

apply himp_inj_prem.


repeat (
match goal with |- ?l ==> ?r => match l with context [ [?p] ] =>
  let H := fresh "H" in
  let f := move_r [p] l in
  pose proof f as H;
  eapply himp_trans; [ apply H |  ];
  eapply himp_trans ; [ | apply rm_emp_l ];
  clear H; apply himp_split
end end
).

SearchAbout (?x * emp ==> ?x).

Print himp_pure.

apply H.

let H := (move_l f (f * a)) in pose proof H.
let H := (move_l f (a * f)) in pose proof H.
let H := (move_l f (a * (b * f))) in pose proof H.
let H := (move_l f ((a * b) * f)) in pose proof H.
let H := (move_l f (a * (b * f) * c)) in pose proof H.
let H := (move_l f (a * (b * f * d) * c)) in pose proof H.

*)
