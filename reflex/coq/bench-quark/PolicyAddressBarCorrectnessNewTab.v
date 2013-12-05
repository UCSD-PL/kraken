Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition UserInput_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS UserInput tt.

Definition Tab_pat id d : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Tab (Some id, (Some d, tt)).

Theorem ensures : forall st tr id d,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Ensures PAYD COMPT COMPS COMPTDEC
    (KOExec PAYD COMPT COMPS None None (Some (Tab_pat id d)))
    (KOSend PAYD COMPT COMPS (Some UserInput_pat)
      (Some (Build_opt_msg PAYD
        AddrAdd (Some id, (Some d, tt)))))
          tr.
Proof.
  Time solve [crush].
Time Qed.
