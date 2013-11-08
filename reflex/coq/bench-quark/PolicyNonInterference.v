Require Import Kernel NIExists Reflex ReflexBase ReflexFin ReflexHVec ReflexFrontend.

Import SystemFeatures.

Definition clblr d (c : comp COMPT COMPS) :=
  match c
  with
  | Build_comp Tab _ cfg =>
    let cfgd := comp_conf_desc COMPT COMPS Tab in
    if str_eq (@shvec_ith _ _ (projT1 cfgd) (projT2 cfgd)
                               cfg 1%fin) d
    then true
    else false
  | Build_comp CProc _ cfg =>
    let cfgd := comp_conf_desc COMPT COMPS CProc in
    if str_eq (@shvec_ith _ _ (projT1 cfgd) (projT2 cfgd)
                               cfg 0%fin) d
    then true
    else false
  | Build_comp UserInput _ _ => true
  | _ => false
  end.

Definition vlblr (f : fin (projT1 KSTD)) := true.

Definition cslblr (c : comp COMPT COMPS) :=
  match c with
  | Build_comp Tab _ _ => true
  | Build_comp UserInput _ _ => true
  | Build_comp Output _ _ => true
  | _ => false
  end.

Local Opaque str_of_string.

Import Language Spec.

Theorem ni : forall d, NI PAYD COMPT COMPTDEC COMPS
  IENVD KSTD INIT HANDLERS (clblr d) vlblr cslblr.
Proof.
  Time solve [ni].
Qed.
