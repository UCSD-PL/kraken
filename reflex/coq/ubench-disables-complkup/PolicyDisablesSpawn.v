Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language.

Definition C_pat n : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS C (Some n, tt).

Theorem disable : forall st tr n,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Disables PAYD COMPT COMPS COMPTDEC
           (KOExec PAYD COMPT COMPS
                   None None (Some (C_pat n)))
           (KOExec PAYD COMPT COMPS
                   None None (Some (C_pat n)))

          tr.
Proof.
  Time solve [crush].
Qed.
