Require Import List.
Require Import Ascii.
Require Import NPeano.
Require Import Ynot.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.

(* syntax *)

Inductive type_t : Set :=
  num_t | str_t | fd_t.

Definition payload_t : Set :=
  list type_t.

Definition msg_spec : Set :=
  list payload_t.

(* semantics *)

(* follow ascii design, little endian *)
Inductive Num : Set :=
| num : ascii -> ascii -> Num.

Definition nat_of_Num (n : Num) : nat :=
  match n with
  | num l h => nat_of_ascii l + nat_of_ascii h * 256
  end.

Definition Num_of_nat (n : nat) : Num :=
  let l := n mod 256 in
  let h := n / 256 in
  num (ascii_of_nat l) (ascii_of_nat h).

Lemma nat_of_ascii_bound :
  forall x, nat_of_ascii x < 256.
Proof.
  destruct x.
  repeat (
    match goal with [ b : bool |- _ ] => destruct b end
  ); compute; omega.
Qed.

Lemma Num_nat_embedding :
  forall (n : Num), Num_of_nat (nat_of_Num n) = n.
Proof with try discriminate.
  destruct n as [[l h]]; simpl.
  unfold Num_of_nat, nat_of_Num.
  repeat f_equal.
  rewrite mod_add... rewrite mod_small. now rewrite ascii_nat_embedding.
  apply nat_of_ascii_bound.
  rewrite div_add... rewrite div_small. simpl. now rewrite ascii_nat_embedding.
  apply nat_of_ascii_bound.
Qed.

Definition Num_eq (n1 n2 : Num) : {n1 = n2} + {n1 <> n2}.
  decide equality; apply ascii_dec.
Defined.

(* prevent sep tactic from unfolding *)
Global Opaque nat_of_Num Num_of_nat Num_eq.

Definition Str : Set :=
  list ascii.

Definition FD : Set :=
  Num.

Definition TypeD (t : type_t) : Set :=
  match t with
  | num_t => Num
  | str_t => Str
  | fd_t  => FD
  end.

Fixpoint PayloadD (p : payload_t) : Set :=
  match p with
  | nil => unit
  | t :: ts => TypeD t * PayloadD ts
  end%type.

Definition PayloadD' (p : option payload_t) : Set :=
  match p with
  | None => False
  | Some p' => PayloadD p'
  end.

Record Msg (ms : msg_spec) : Set :=
  { tag : Num
  ; pay : PayloadD' (List.nth_error ms (nat_of_Num tag))
  }.

Inductive Action : Set :=
| Recv   : FD -> Str -> Action
| Send   : FD -> Str -> Action
| RecvFD : FD -> FD  -> Action (* RecvFD f f' : use f to recv f' *)
| SendFD : FD -> FD  -> Action (* SendFD f f' : use f to send f' *)
.

Definition Trace : Set := list Action.

Axiom traced : Trace -> hprop.

Inductive Perm : Set :=
  RecvP | SendP | RecvFDP | SendFDP.

Axiom open : FD -> list Perm -> hprop.

Axiom recv :
  forall (f : FD) (ps : list Perm) (n : Num) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps])
        (fun s : Str => tr ~~ traced (Recv f s :: tr) * open f ps *
          [nat_of_Num n = List.length s]).

Axiom send :
  forall (f : FD) (ps : list Perm) (s : Str) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps])
        (fun _ : unit => tr ~~ traced (Send f s :: tr) * open f ps).

Axiom recv_fd :
  forall (f : FD) (ps : list Perm) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvFDP ps])
        (fun f' : FD => tr ~~ traced (RecvFD f f' :: tr) * open f ps).

Axiom send_fd :
  forall (f : FD) (ps : list Perm) (f' : FD) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendFDP ps])
        (fun _ : unit => tr ~~ traced (SendFD f f' :: tr) * open f ps).

(* we use big endian to follow network order *)
Definition RecvNum (f : FD) (n : Num) : Trace :=
  match n with
  | num l h => Recv f (h :: l :: nil) :: nil
  end.

Definition SendNum (f : FD) (n : Num) : Trace :=
  match n with
  | num l h => Send f (h :: l :: nil) :: nil
  end.

Definition RecvStr (f : FD) (s : Str) : Trace :=
  Recv f s :: RecvNum f (Num_of_nat (List.length s)).

Definition SendStr (f : FD) (s : Str) : Trace :=
  Send f s :: SendNum f (Num_of_nat (List.length s)).

Definition recv_num:
  forall (f : FD) (ps : list Perm) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps])
        (fun n : Num => tr ~~ traced (RecvNum f n ++ tr) * open f ps).
Proof.
  intros; refine (
    s <- recv f ps (num "002" "000") tr;
    match s with
    | h :: l :: nil =>
      {{ Return (num l h) }}
    | _ => (* bogus *)
      {{ Return (num "000" "000") }}
    end
  );
  sep fail idtac;
  discriminate.
Qed.

Definition send_num:
  forall (f : FD) (ps : list Perm) (n : Num) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps])
        (fun _ : unit => tr ~~ traced (SendNum f n ++ tr) * open f ps).
Proof.
  intros; refine (
    match n with
    | num l h =>
      send f ps (h :: l :: nil) tr;;
      {{ Return tt }}
    end
  );
  sep fail idtac.
Qed.

Definition recv_str:
  forall (f : FD) (ps : list Perm) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps])
        (fun s : Str => tr ~~ traced (RecvStr f s ++ tr) * open f ps).
Proof.
  intros; refine (
    n <- recv_num f ps tr <@> [In RecvP ps];
    s <- recv f ps n (tr ~~~ RecvNum f n ++ tr);
    {{ Return s }}
  );
  sep fail idtac.
  rewrite <- H.
  rewrite Num_nat_embedding.
  sep fail idtac.
Qed.

Definition send_str:
  forall (f : FD) (ps : list Perm) (s : Str) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps])
        (fun (_ : unit) => tr ~~ traced (SendStr f s ++ tr) * open f ps).
Proof.
  intros; refine (
    let n := Num_of_nat (List.length s) in
    send_num f ps n tr <@> [In SendP ps];;
    send f ps s (tr ~~~ SendNum f n ++ tr);;
    {{ Return tt }}
  );
  sep fail idtac.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque RecvNum SendNum RecvStr SendStr.

Definition RecvType (f : FD) (t : type_t) : TypeD t -> Trace :=
  match t with
  | num_t => fun n : Num => RecvNum f n
  | str_t => fun s : Str => RecvStr f s
  | fd_t  => fun g : FD  => RecvFD  f g :: nil
  end.

Definition SendType (f : FD) (t : type_t) : TypeD t -> Trace :=
  match t with
  | num_t => fun n : Num => SendNum f n
  | str_t => fun s : Str => SendStr f s
  | fd_t  => fun g : FD  => SendFD  f g :: nil
  end.

Fixpoint RecvPay (f : FD) (pt : payload_t) : PayloadD pt -> Trace :=
  match pt with
  | nil => fun _ : unit =>
      nil
  | t :: ts => fun pv : TypeD t * PayloadD ts =>
      match pv with
      | (v, vs) => RecvType f t v ++ RecvPay f ts vs
      end
  end.

Fixpoint SendPay (f : FD) (pt : payload_t) : PayloadD pt -> Trace :=
  match pt with
  | nil => fun _ : unit =>
      nil
  | t :: ts => fun pv : TypeD t * PayloadD ts =>
      match pv with
      | (v, vs) => SendType f t v ++ SendPay f ts vs
      end
  end.

Definition RecvPay' (f : FD) (pt : option payload_t) : PayloadD' pt -> Trace :=
  match pt with
  | None => fun p : False =>
      False_rec Trace p
  | Some pt' => fun p : PayloadD pt' =>
      RecvPay f pt' p
  end.

Definition SendPay' (f : FD) (pt : option payload_t) : PayloadD' pt -> Trace :=
  match pt with
  | None => fun p : False =>
      False_rec Trace p
  | Some pt' => fun p : PayloadD pt' =>
      SendPay f pt' p
  end.

Definition RecvMsg (ms : msg_spec) (f : FD) (m : Msg ms) : Trace :=
   let t := tag ms m in
   let pt := List.nth_error ms (nat_of_Num t) in
   RecvPay' f pt (pay ms m) ++ RecvNum f t.

Definition SendMsg (ms : msg_spec) (f : FD) (m : Msg ms) : Trace :=
   let t := tag ms m in
   let pt := List.nth_error ms (nat_of_Num t) in
   SendPay' f pt (pay ms m) ++ SendNum f t.


Definition recv_type :
  forall (f : FD) (ps : list Perm) (t : type_t) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
        (fun v : TypeD t => tr ~~ traced (RecvType f t v ++ tr) * open f ps).
Proof.
  intros; refine (
    match t with
    | num_t =>
        (* Num = TypeD t here but I can't get the match to go through ! *)
        n <- recv_num f ps tr;
        {{ Return n }}
    | str_t =>
        s <- recv_str f ps tr;
        {{ Return s }}
    | fd_t =>
        g <- recv_fd f ps tr;
        {{ Return g }}
    end
  );
  sep fail auto.
  repeat rewrite app_ass; simpl;
  sep fail auto.
Qed.