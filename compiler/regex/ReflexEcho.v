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

Definition NB_MSG : nat := 1.

Definition PDV : payload_desc_vec NB_MSG :=
  ( existT _ 1 (str_d, tt)
  , tt
  ).

Definition HANDLERS : @handler NB_MSG PDV :=
  (fun m =>
    match tag m as _tm return
      @sdenote _ SDenoted_payload_desc (@lkup_tag NB_MSG PDV _tm) -> _
    with
    | None => fun pl =>
      let (s, _) := pl in
         Send m (CurChan m) (MsgExpr m None (SLit m s, tt))
      :: nil
    | Some bad => fun _ =>
      match bad with end
    end (pay m)
  )
.

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

Ltac get_leftmost RE :=
  match RE with
  | RE_Atom ?A => A
  | RE_NAtom ?A => A
  | RE_Any => constr:"."
  | RE_Star ?R => get_leftmost R
  | RE_Alt ?R1 ?R2 => get_leftmost R1
  | RE_Concat ?R1 ?R2 => get_leftmost R1
  end.

Ltac match_dec oact act :=
  match oact with
  | KOSend ?ofd ?omsg => match act with
                         | KSend ?fd ?msg
      => assert (decide (argMatch ofd fd /\ msgMatch omsg msg)
                 (*~(argMatch ofd fd /\ msgMatch omsg msg)*))
                         end
  end.

Ltac match_cond oact act :=
   match oact with
   | KOSend ?ofd ?omsg => match act with
                         | KSend ?fd ?msg
                          => constr:(argMatch ofd fd
                                     /\ msgMatch omsg msg)
                         end
   end.

Ltac nmatch_cond oact act :=
   match oact with
   | KOSend ?ofd ?omsg => match act with
                         | KSend ?fd ?msg
                          => constr:(~(argMatch ofd fd)
                                     \/ ~(msgMatch omsg msg))
                         end
   end.

Ltac act_cond act RE :=
  match RE with
  | RE_Atom ?oact => match_cond oact act
  | RE_NAtom ?oact => nmatch_cond oact act
  | RE_Any => True
  | RE_Star ?R => act_cond act R
  | RE_Alt ?R1 ?R2 => let l_cond := act_cond act R1 in
                      let r_cond := act_cond act R2 in
                      constr:(l_cond \/ r_cond)
  | RE_Concat ?R1 _ => act_cond act R1
  end.

Lemma stupid : forall P:Prop, P -> (P /\ True).
Proof.
  auto.
Qed.

Theorem echo_var : forall st tr m,
  Reach HANDLERS st -> inhabits tr = ktr st ->
  RMatch (echo_re_var m) tr.
Proof.
  intros.
  unfold echo_re_var.
  generalize dependent tr.
  induction H; intros; simpl in *.
    unpack.
    matchRE NB_MSG.

    destruct_msg.
    unpack.
    compute.
    match goal with
    |- RMatch ?re (?act::_)
       => let cond := act_cond act re in assert cond
    end.
    computeMsgMatch NB_MSG.
      admit.

    destruct H4.
      revert H4.
      computeMsgMatch NB_MSG.
      matchRE NB_MSG.

      idtac.
      revert H4.
      computeMsgMatch NB_MSG.
      matchRE NB_MSG.
      idtac.

    match goal with
    |- RMatch ?re (?act::_)
       => let oact := get_leftmost re in
          match_dec oact act
    end.
    computeMsgMatch NB_MSG.
    
    cut (decide (m = s0)).
    tauto.
    apply str_eq.

    destruct H4.
    destruct H4.
    revert H5.
    computeMsgMatch NB_MSG.
    matchRE NB_MSG.
    idtac.

    revert H4.
    computeMsgMatch NB_MSG.
    matchRE NB_MSG.

    unpack.
    matchRE NB_MSG.

    unpack.
    matchRE NB_MSG.
Qed.

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