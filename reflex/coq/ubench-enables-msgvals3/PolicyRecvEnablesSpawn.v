Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language.

Require Import PolLang.
Require Import ActionMatch.

Local Opaque str_of_string.

Definition C1_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS C1 tt.

Definition C2_pat n s : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS C2 (Some n, (Some s, tt)).

Theorem enable : forall st tr n s,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
          (KORecv PAYD COMPT COMPS (Some C1_pat)
                  (Some (Build_opt_msg PAYD
                                       M (Some n, (Some s, tt)))))
          (KOExec PAYD COMPT COMPS None None (Some (C2_pat n s)))
          tr.
Proof.
  Time crush.
Qed.
