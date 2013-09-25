Require Import String.
Require Import Reflex ReflexBase ReflexFrontend.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language.

Require Import PolLang.
Require Import ActionMatch.
Require Import List.

Local Opaque str_of_string.

Theorem immafter st tr :
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmAfter PAYD COMPT COMPS COMPTDEC
           (KOExec PAYD COMPT COMPS (*Some (str_of_string "comp2.py")*) None None
                   (Some (@Build_conc_pat COMPT COMPS C2 tt))
           )
           (KOExec PAYD COMPT COMPS (*Some (str_of_string "comp1.py")*) None None
                   (Some (@Build_conc_pat COMPT COMPS C1 tt))
           )
           tr.
Proof.
  crush.
Qed.
