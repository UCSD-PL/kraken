Require Import String.

Require Import Reflex.
Require Import ReflexFin.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import Regex.
Require Import Ynot.
Require Import List.
Require Import RegexTacs.
Require Import ReflexEcho.

Definition send_star :=
  RE_Star (RE_Alt (RE_Atom (@KOSelect NB_MSG PDV None None))
                  (RE_Alt (RE_Atom (@KORecv NB_MSG PDV None None))
                          (RE_Alt (RE_Atom (@KOSend NB_MSG PDV None None))
                                  (RE_Alt (RE_Atom
                                             (@KOExec NB_MSG PDV None None None))
                                          (RE_Atom
                                             (@KOBogus NB_MSG PDV None None)))))).

Definition echo_re :=
  RE_Star
    (RE_Alt
       (RE_NAtom (@KOSend NB_MSG PDV None
                          (Some (@Build_opt_msg NB_MSG PDV
                                                None (None, tt)))))
       (RE_Concat
          (RE_Atom (@KOSend NB_MSG PDV None
                            (Some (@Build_opt_msg NB_MSG PDV
                                                  None (None, tt)))))
          (RE_Atom (@KORecv NB_MSG PDV None
                            (Some (@Build_opt_msg NB_MSG PDV
                                                  None (None, tt))))))).

Definition echo_re_var m :=
  RE_Star
    (RE_Alt
       (RE_NAtom (@KOSend NB_MSG PDV None
                          (Some (@Build_opt_msg NB_MSG PDV
                                                None (Some m, tt)))))
       (RE_Concat
          (RE_Atom (@KOSend NB_MSG PDV None
                            (Some (@Build_opt_msg NB_MSG PDV
                                                  None (Some m, tt)))))
          (RE_Atom (@KORecv NB_MSG PDV None
                            (Some (@Build_opt_msg NB_MSG PDV
                                                  None (Some m, tt))))))).

Theorem always_send : forall st tr,
  Reach HANDLERS st -> inhabits tr = ktr st ->
  RMatch send_star tr.
Proof.
  intros.
  unfold send_star.
  generalize dependent tr.
  induction H; intros; simpl in *;
  try destruct_msg; unpack; matchRE NB_MSG.
Qed.

Theorem echo : forall st tr,
  Reach HANDLERS st -> inhabits tr = ktr st ->
  RMatch echo_re tr.
Proof.
  intros.
  unfold echo_re.
  generalize dependent tr.
  induction H; intros; simpl in *;
  try destruct_msg; unpack; matchRE NB_MSG.
Qed.