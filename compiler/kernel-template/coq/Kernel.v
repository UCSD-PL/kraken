Require Import List.
Require Import Ascii.
Require Import Ynot.
Require Import KrakenBase.
Require Import Exchange.

Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Record kstate : Set :=
  mkst { c : chan
       ; ktr : [Trace]
       }.

Inductive KTrace : Trace -> Prop :=
| KT_init :
  KTrace nil
| KT_iter :
  forall tr1 tr2,
  KTrace tr1 ->
  AddedValidExchange tr1 tr2 ->
  KTrace tr2.

Definition kstate_inv s : hprop :=
  tr :~~ ktr s in
  traced tr * [KTrace tr] * bound (c s).

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  unfold kstate_inv; intros [c tr];
  refine (
    tr' <- exchange c tr <@> (tr ~~ [KTrace tr]);
    {{ Return (mkst c tr') }}
  );
  sep fail auto;
  apply himp_pure';
  econstructor; eauto.
Qed.

Definition kloop:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  intros; refine (
    Fix
      (fun s => kstate_inv s)
      (fun s s' => kstate_inv s')
      (fun self s =>
        s <- kbody s;
        s <- self s;
        {{ Return s }}
      )
    s
  );
  sep fail auto.
Qed.

Axiom dummy : chan.

Definition main:
  forall (_ : unit),
  STsep (traced nil * bound dummy)
        (fun s' => kstate_inv s').
Proof.
  intros; refine (
    s' <- kloop (mkst dummy [nil]);
    {{ Return s' }}
  );
  unfold kstate_inv;
  sep fail auto.
  apply himp_pure'; constructor; auto.
Qed.
