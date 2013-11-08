Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition Tab_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Tab (None, (None, tt)).

Theorem imm_after : forall st tr f,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmAfter PAYD COMPT COMPS COMPTDEC
    (KOSend PAYD COMPT COMPS (Some (Tab_pat))
            (Some (Build_opt_msg PAYD
                                 CookieProcessRegister (Some f, tt))))
    (KOCall PAYD COMPT COMPS
            (Some (str_of_string create_ckchan)) (Some nil) (Some f))
    tr.
Proof.
  Time solve [crush].
Qed.
