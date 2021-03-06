Require Import String.
Require Import Reflex ReflexBase ReflexFin.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Require Import NIExists.

Definition clblr (c : comp COMPT COMPS) :=
  match comp_type _ _ c with
  | Echo1 => true
  | Echo2 => false
  end.

Definition vlblr (f : fin (projT1 KSTD)) : bool :=
  match f with
  | None => true
  | Some None => false
  | Some (Some bad) => match bad with end
  end.

Definition cslblr (c : comp COMPT COMPS) := true.

Theorem ni : NI PAYD COMPT COMPTDEC COMPS
  IENVD KSTD INIT HANDLERS clblr vlblr cslblr.
Proof.
  Time solve [ni].
Qed.
