Require Import List.
Require Import Ascii.
Require Import BinNat.
Require Import Nnat.
Require Import Ynot.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

Definition str : Set :=
  list ascii.

Definition len (s: str) : N :=
  N_of_nat (length s).

Axiom chan : Set.

Inductive Action : Set :=
| RecvN : chan -> N -> Action
| RecvS : chan -> N -> str -> Action
| SendN : chan -> N -> Action
| SendS : chan -> str -> Action.

Definition Trace : Set :=
  list Action.

Definition RecvNum (c: chan) (n: N) : Trace :=
  RecvN c n ::
  nil.

Definition SendNum (c: chan) (n: N) : Trace :=
  SendN c n ::
  nil.

Definition RecvStr (c: chan) (s: str) : Trace :=
  RecvS c (len s) s ::
  RecvN c (len s) ::
  nil.

Definition SendStr (c: chan) (s: str) : Trace :=
  SendS c s ::
  SendN c (len s) ::
  nil.

Axiom bound : chan -> hprop.
Axiom traced : Trace -> hprop.

Axiom recvN:
  forall (c: chan) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun n => tr ~~ traced (RecvN c n :: tr) * bound c).

Axiom recvS:
  forall (c: chan) (n: N) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun s => tr ~~ traced (RecvS c n s :: tr) * bound c * [n = len s]).

Axiom sendN:
  forall (c: chan) (n: N) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_: unit) => tr ~~ traced (SendN c n :: tr) * bound c).

Axiom sendS:
  forall (c: chan) (s: str) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_: unit) => tr ~~ traced (SendS c s :: tr) * bound c).

Definition recvNum:
  forall (c: chan) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun n => tr ~~ traced (RecvNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    n <- recvN c
      tr;
    {{ Return n }}
  );
  sep fail auto.  
Qed.

Definition sendNum:
  forall (c: chan) (n: N) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_: unit) => tr ~~ traced (SendNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    sendN c n
      tr;;
    {{ Return tt }}
  );
  sep fail auto.  
Qed.

Definition recvStr:
  forall (c: chan) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun s => tr ~~ traced (RecvStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    n <- recvN c
      tr;
    s <- recvS c n
      (tr ~~~ RecvN c n :: tr);
    {{ Return s }}
  );
  sep fail auto.  
Qed.

Definition sendStr:
  forall (c: chan) (s: str) (tr: [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_: unit) => tr ~~ traced (SendStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    sendN c (len s)
      tr;;
    sendS c s
      (tr ~~~ SendN c (len s) :: tr);;
    {{ Return tt }}
  );
  sep fail auto.  
Qed.