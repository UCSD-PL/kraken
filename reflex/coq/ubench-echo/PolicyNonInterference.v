Require Import String.
Require Import Reflex ReflexBase ReflexFin.
Require Import Kernel.

Import SystemFeatures Language Spec.

Require Import NIExists.

Require Import Ynot.
Require Import NITactics.

Definition clblr (c : comp COMPT COMPS) :=
  match comp_type _ _ c with
  | Echo1 => true
  | Echo2 => false
  end.

Definition vlblr (f : fin (projT1 KSTD)) : bool :=
  match f with end.

Theorem ni : NI PAYD COMPT COMPTDEC COMPS
  IENVD KSTD INIT HANDLERS clblr vlblr.
Proof.
  Time ni.
Qed.
