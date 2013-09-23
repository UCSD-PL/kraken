Require Import String.
Require Import Reflex ReflexBase ReflexFin.
Require Import Kernel.

Import SystemFeatures Language Spec.

Require Import NIExists.
Require Import PruneFacts.

Definition clblr (c : comp COMPT COMPS) :=
  match comp_type _ _ c with
  | Engine => true
  | _      => false
  end.

Definition vlblr (f : fin (projT1 KSTD)) := false.

Local Opaque str_of_string.

Theorem ni : NI PAYD COMPT COMPTDEC COMPS
  IENVD KSTD INIT HANDLERS clblr vlblr.
Proof.
  Time ni.
Qed.
