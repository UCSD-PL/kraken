Require Import List.
Require Import Ascii.
Require Import BinNat.
Require Import Nnat.
Require Import Ynot.

Require Import KrakenBase.
Require Import Turn.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Inductive KTrace : Trace -> Prop :=
| KT_init :
  KTrace nil
| KT_iter :
  forall tr c m,
  KTrace tr ->
  KTrace (SendMsgs c (protocol m) ++ RecvMsg c m ++ tr).

Definition kloop:
  forall (c: chan) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c * [KTrace tr])
        (fun (tr': [Trace]) => tr' ~~ traced tr' * bound c * [KTrace tr']).
Proof.
  intros; refine (
    Fix2
      (fun (_: unit) (tr: [Trace]) => tr ~~ traced tr * bound c * [KTrace tr])
      (fun (_: unit) (tr tr': [Trace]) => tr' ~~ traced tr' * bound c * [KTrace tr'])
      (fun self (_: unit) (tr: [Trace]) =>
        req <- turn c
          tr <@>
          (tr ~~ [KTrace tr]);
        tr' <- self tt
          (tr ~~~ SendMsgs c (protocol req) ++ RecvMsg c req ++ tr) <@>
          (tr ~~ [KTrace tr]);
        {{ Return  tr' }})
      tt tr
  );
  sep fail auto.
  apply himp_pure'.
  constructor; auto.
Qed.

Axiom c : chan.

Definition main:
  forall (_: unit),
  STsep (traced nil * bound c)
        (fun (tr: [Trace]) => tr ~~ traced tr * bound c * [KTrace tr]).
Proof.
  intros; refine (
    tr' <- kloop c
      [nil];
    {{ Return tr' }}
  );
  sep fail auto.
  apply himp_pure'.
  constructor; auto.
Qed.
