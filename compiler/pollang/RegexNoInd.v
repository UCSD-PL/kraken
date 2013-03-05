Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexVec.
Require Import ReflexHVec.

Inductive OptTag : Type :=
C_opttag : vdesc -> OptTag.

Definition soptdenote_desc (d : desc) : Set :=
  option (sdenote_desc d).

Definition soptdenote_vdesc' n (pt : vdesc' n) : Set :=
  shvec soptdenote_desc pt.

Instance SOptDenoted_payload_desc : SDenoted OptTag :=
{ sdenote := fun opttag => match opttag with
                           | C_opttag pd =>
                             soptdenote_vdesc' (projT1 pd) (projT2 pd)
                           end
}.

Section KOAction.

Context {NB_MSG:nat}.
Context {PLT:vvdesc NB_MSG}.

Record opt_msg : Set :=
  { opt_tag : fin NB_MSG
  ; opt_pay : s[[ C_opttag (@lkup_tag NB_MSG PLT opt_tag) ]]
  }.

(*Definition KTrace := KTrace NB_MSG PLT.*)
(*Definition KAction := KAction NB_MSG PLT.*)

Inductive KOAction : Set :=
| KOExec   : option str -> option (list str) -> option fd -> KOAction
| KOCall   : option str -> option (list str) -> option fd -> KOAction
| KOSelect : option (list fd) -> option fd -> KOAction
| KOSend   : option fd -> option opt_msg -> KOAction
| KORecv   : option fd -> option opt_msg -> KOAction
| KOBogus  : option fd -> option num -> KOAction.

Inductive Regexp : Type :=
| RE_Atom   : KOAction -> Regexp
| RE_NAtom  : KOAction -> Regexp
| RE_Any    : Regexp
| RE_Alt    : Regexp -> Regexp -> Regexp
| RE_Star   : Regexp -> Regexp
| RE_Concat : Regexp -> Regexp -> Regexp.

Definition argMatch {T:Type} (opt:option T) (arg:T) : Prop :=
  match opt with
  | None   => True
  | Some t => t = arg
  end.

Fixpoint unpackedPLMatch n (pd:vdesc' n)
                           (opt_pl:soptdenote_vdesc' n pd)
                           (pl:sdenote_vdesc' n pd) : Prop :=
  match n as _n
  return forall (pd' : vdesc' _n),
         soptdenote_vdesc' _n pd' ->
         sdenote_vdesc' _n pd' ->
         Prop
  with
  | O => fun _ _ _ => True
  | S n' => fun pd opt_pl pl =>
    match pd as _pd return
      soptdenote_vdesc' (S n') _pd ->
      sdenote_vdesc' (S n') _pd ->
      Prop
    with
    | (t, pd') => fun opt_pl pl =>
      match opt_pl, pl with
      | (aopt, vopt), (a, v) =>
        argMatch aopt a /\ unpackedPLMatch n' pd' vopt v
      end
    end opt_pl pl
  end pd opt_pl pl.

Definition packedPLMatch
  (tag:fin NB_MSG)
  (opt_pay:s[[C_opttag (@lkup_tag NB_MSG PLT tag)]])
  (pay:s[[@lkup_tag NB_MSG PLT tag]]) : Prop :=
  match @lkup_tag NB_MSG PLT tag as _l return
        s[[C_opttag _l ]] -> s[[ _l ]] -> Prop
  with
  | existT n pl' => unpackedPLMatch n pl'
  end opt_pay pay.

Definition msgMatch' (opt_pl:opt_msg) (pl:msg) : Prop :=
  let opt_tag := (opt_tag opt_pl) in
  let tag := (tag pl) in
  match fin_eq_dec tag opt_tag with
  | left H => match H in eq _ _tag return
                s[[C_opttag (@lkup_tag NB_MSG PLT _tag)]] -> Prop
              with
              | eq_refl => fun opt_pay =>
                 packedPLMatch tag opt_pay (pay pl)
              end (opt_pay opt_pl)
  | right H => False
  end.

Definition msgMatch (opt_pl:option opt_msg) (pl:msg) : Prop :=
  match opt_pl with
  | None => True
  | Some opt_pl' => msgMatch' opt_pl' pl
  end.

Definition AMatch (oact:KOAction) (act:@KAction NB_MSG PLT) : Prop :=
match oact, act with
| KOExec s ls f, KExec s' ls' f' => argMatch s s'
                                      /\ argMatch ls ls'
                                      /\ argMatch f f'
| KOCall s ls f, KCall s' ls' f' => argMatch s s'
                                      /\ argMatch ls ls'
                                      /\ argMatch f f'
| KOSelect lfd f, KSelect lfd' f' => argMatch lfd lfd'
                                       /\ argMatch f f'
| KOSend f omsg, KSend f' amsg => argMatch f f'
                                   /\ msgMatch omsg amsg
| KORecv f omsg, KRecv f' amsg => argMatch f f'
                                   /\ msgMatch omsg amsg
(**I don't know if this is the right thing to do for KBogus matching.
   It just checks if the message tags and fds are the same**)
| KOBogus f optbtag, KBogus f' bmsg => argMatch f f'
                                         /\ argMatch optbtag (btag bmsg)
| _, _ => False
end.

Inductive RMatch : Regexp -> @KTrace NB_MSG PLT -> Prop :=
| RM_Atom     : forall a a', AMatch a a' ->
                             RMatch (RE_Atom a) (a'::nil)
| RM_NAtom    : forall a a', ~ AMatch a a' ->
                             RMatch (RE_NAtom a) (a'::nil)
| RM_Any      : forall a, RMatch (RE_Any) (a::nil)
| RM_Alt      : forall re re' tr, RMatch re tr \/ RMatch re' tr ->
                                  RMatch (RE_Alt re re') tr
| RM_StarInit : forall re, RMatch (RE_Star re) nil
| RM_Star     : forall re tr tr', RMatch (RE_Star re) tr ->
                                  RMatch re tr' ->
                                  RMatch (RE_Star re) (tr' ++ tr)
| RM_Concat   : forall re re' tr tr', RMatch re tr ->
                                      RMatch re' tr' ->
                                      RMatch (RE_Concat re re') (tr ++ tr').

End KOAction.


Ltac decide_act :=
  match goal with
  | [ H : decide (?a0) |- decide (?a0 /\ ?a1 /\ ?a2) ]
      => destruct H; cut (decide (a1 /\ a2)); try tauto
  | [ H : decide (?a0) |- decide (?a0 /\ ?a1) ]
      => destruct H; cut (decide (a1)); try tauto
  | [ H : decide (?a) |- decide (?a) ]
      => auto
  | [ |- context[argMatch ?o ?s] ]
      => let H := fresh "H" in assert (decide (argMatch o s)) as H by
         (destruct o; simpl; (repeat decide equality) || auto)
  end.

Ltac reduceMsgMatch :=
  match goal with
  | [ |- context[fin_eq_dec ?f1 ?f2] ]
    => destruct (fin_eq_dec f1 f2)
  | [ Heq : _ = ?fin |- context[match ?Heq with | eq_refl => _ end] ]
    => destruct Heq
  end.

Definition decide_payload : forall NB_MSG PDV tag opl pl,
                              decide (@packedPLMatch NB_MSG PDV tag opl pl).
Proof.
  intros.
  unfold packedPLMatch.
  destruct (@lkup_tag NB_MSG PDV tag).
  induction x.
    auto.

    simpl in *.
    destruct v.
    simpl in *.
    destruct opl.
    destruct pl.
    simpl in *.
    destruct s.
    destruct d; simpl in *;
    assert (decide (s = s1)) by repeat decide equality;
    decide_act; auto.
    simpl.
    cut (decide (unpackedPLMatch x v s0 s2)).
    tauto.
    auto.
Defined.

Definition decide_msg : forall NB_MSG PDV omsg msg,
                          decide (@msgMatch NB_MSG PDV omsg msg).
Proof.
  intros.
  destruct omsg.
    destruct msg.
    destruct o.
    simpl.
    unfold msgMatch'.
    reduceMsgMatch.
    simpl in *.
    reduceMsgMatch.
    apply decide_payload.
    auto.
    auto.
Defined.

Definition decide_act : forall NB_MSG PDV oact act,
                          decide (@AMatch NB_MSG PDV oact act).  
Proof.
  intros. destruct act; destruct oact; simpl in *; auto.
    repeat decide_act.

    repeat decide_act.

    repeat decide_act.

    repeat decide_act;
    apply decide_msg.

    repeat decide_act;
    apply decide_msg.

    repeat decide_act.
Defined.