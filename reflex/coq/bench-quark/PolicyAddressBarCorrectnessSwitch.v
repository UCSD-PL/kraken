Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition UserInput_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS UserInput tt.

Definition Output_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Output tt.

Theorem imm_after : forall st tr id,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmAfter PAYD COMPT COMPS COMPTDEC
    (KOSend PAYD COMPT COMPS (Some (Output_pat))
            (Some (Build_opt_msg PAYD
                                RenderCompleted (Some id, tt))))
    (KOSend PAYD COMPT COMPS (Some (UserInput_pat))
            (Some (Build_opt_msg PAYD
                                AddrFocus (Some id, tt))))
    tr.
Proof.
  crush. unfold Reflex.match_comp, Reflex.match_comp_pf in *. simpl in *.
  Time solve [crush].
Time Qed.