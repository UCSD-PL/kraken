Require Import Ascii.
Require Import List.
Require Import NPeano.
Require Import String.
Require Import Ynot.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Definition str : Set := list ascii.

(* /!\ Making this a flat pair leads to problems in later proofs. *)
Inductive num : Set := Num : ascii * ascii -> num.

Lemma nat_of_ascii_bound: forall x, nat_of_ascii x < 256.
Proof.
  destruct x.
  repeat (match goal with [b : bool |- _] => destruct b end); compute; omega.
Qed.

Definition nat_of_num (n : num) : nat :=
  match n with
  | Num (l, h) => nat_of_ascii l + nat_of_ascii h * 256
  end.

Definition num_of_nat (n : nat) : num :=
  let l := n mod 256 in
  let h := n / 256 in
  Num (ascii_of_nat l, ascii_of_nat h).

Lemma num_nat_embedding :
  forall (n : num), num_of_nat (nat_of_num n) = n.
Proof with try discriminate.
  destruct n as [[l h]]; simpl.
  unfold num_of_nat, nat_of_num.
  repeat f_equal.
  rewrite mod_add... rewrite mod_small. now rewrite ascii_nat_embedding.
  apply nat_of_ascii_bound.
  rewrite div_add... rewrite div_small. simpl. now rewrite ascii_nat_embedding.
  apply nat_of_ascii_bound.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque nat_of_num num_of_nat.

Fixpoint str_of_string (s: string): str :=
  match s with
  | EmptyString => nil
  | String c rest => c :: str_of_string rest
  end.



Inductive chan_type : Set :=
| System
| Slave
.

Definition chan_path (t: chan_type): str :=
  match t with
  | System => str_of_string "system"
  | Slave => str_of_string "slave"
  end.

Axiom chan : chan_type -> Set.

Record st_System := {  }.
Record st_Slave := {  }.

Definition comp_state (t: chan_type) : Set :=
  match t with
  | System => st_System
  | Slave => st_Slave
  end.

Definition tchan := sigT (fun t : chan_type => (chan t * comp_state t)%type).

Axiom tchan_eq : forall (c1 c2 : tchan), { c1 = c2 } + { c1 <> c2 }.

Lemma tchan_eq_true :
  forall (c : tchan) (A : Type) (vT vF : A),
  (if tchan_eq c c then vT else vF) = vT.
Proof.
  intros; case (tchan_eq c c); auto. congruence.
Qed.

Lemma tchan_eq_false :
  forall (c1 c2 : tchan) (A : Type) (vT vF : A),
  c1 <> c2 ->
  (if tchan_eq c1 c2 then vT else vF) = vF.
Proof.
  intros; case (tchan_eq c1 c2); auto. congruence.
Qed.

Axiom fdesc : Set.

Inductive Action : Set :=
| Exec   : str -> tchan -> Action
| Call   : str -> str -> fdesc -> Action
| Select : list tchan -> tchan -> Action
| Recv   : tchan -> str -> Action
| Send   : tchan -> str -> Action
| RecvFD : tchan -> fdesc -> Action
| SendFD : tchan -> fdesc -> Action
.

Definition Trace : Set := list Action.

Axiom traced : Trace -> hprop.

Axiom bound : tchan -> hprop.

Axiom exec :
  forall (t: chan_type) (prog : str) (st: comp_state t) (tr : [Trace]),
    STsep (tr ~~ traced tr * [prog = chan_path t])
    (fun (c: tchan) =>
      tr ~~ bound c * traced (Exec prog c :: tr) * [projT1 c = t]).

Axiom call :
  forall (prog arg : str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun (f : fdesc) => tr ~~ traced (Call prog arg f :: tr)).

(* TODO add non-empty precondition *)
Axiom select :
  forall (chans : list tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun (c : tchan) => tr ~~ traced (Select chans c :: tr) * [In c chans]).

Axiom recv :
  forall (c : tchan) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (s : str) => tr ~~ traced (Recv c s :: tr) * bound c *
          [nat_of_num n = List.length s]).

Axiom send :
  forall (c : tchan) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (Send c s :: tr) * bound c).

Axiom recv_fd :
  forall (c : tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (f : fdesc) => tr ~~ traced (RecvFD c f :: tr) * bound c).

Axiom send_fd :
  forall (c : tchan) (f : fdesc) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendFD c f :: tr) * bound c).

Definition RecvNum (c : tchan) (n : num) : Trace :=
  match n with
  | Num (l, h) => Recv c (h :: l :: nil) :: nil
  end.

Definition recv_num:
  forall (c : tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (n : num) => tr ~~ traced (RecvNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    s <- recv c (Num ("002", "000")) tr;
    match s with
    | h :: l :: nil =>
      {{ Return (Num (l, h)) }}
    | _ => (* bogus *)
      {{ Return (Num ("000", "000")) }}
    end
  );
  sep fail auto;
  compute in H; discriminate.
Qed.

Definition SendNum (c : tchan) (n : num) : Trace :=
  match n with
  | Num (l, h) => Send c (h :: l :: nil) :: nil
  end.

Definition send_num:
  forall (c : tchan) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    match n with
    | Num (l, h) =>
      send c (h :: l :: nil) tr;;
      {{ Return tt }}
    end
  );
  sep fail auto.
Qed.

Definition RecvStr (c : tchan) (s : str) : Trace :=
  Recv c s :: RecvNum c (num_of_nat (List.length s)).

Definition recv_str:
  forall (c : tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (s : str) => tr ~~ traced (RecvStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    n <- recv_num c tr;
    s <- recv c n (tr ~~~ RecvNum c n ++ tr);
    {{ Return s }}
  );
  sep fail auto.
  rewrite <- H.
  rewrite num_nat_embedding.
  sep fail auto.
Qed.

Definition SendStr (c : tchan) (s : str) : Trace :=
  Send c s :: SendNum c (num_of_nat (List.length s)).

Definition send_str:
  forall (c : tchan) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    let n := num_of_nat (List.length s) in
    send_num c n tr;;
    send c s (tr ~~~ SendNum c n ++ tr);;
    {{ Return tt }}
  );
  sep fail auto.
Qed.

(* trace versions of basic actions so we can always use app (++) *)

Definition Exec_t (prog : str) (c : tchan) : Trace :=
  Exec prog c :: nil.

Definition Call_t (prog arg : str) (f : fdesc) : Trace :=
  Call prog arg f :: nil.

Definition RecvFD_t (c : tchan) (f : fdesc) : Trace :=
  RecvFD c f :: nil.

Definition SendFD_t (c : tchan) (f : fdesc) : Trace :=
  SendFD c f :: nil.

(* prevent sep tactic from unfolding *)
Global Opaque RecvStr SendStr Exec_t Call_t RecvFD_t SendFD_t.

Inductive msg : Set :=
| LoginReq : str -> msg
| LoginRes : num -> msg
| PubkeyReq : msg
| PubkeyRes : str -> msg
| KeysignReq : str -> msg
| KeysignRes : str -> msg
| CreatePtyerReq : msg
| CreatePtyerRes : fdesc -> fdesc -> msg
| SysLoginReq : str -> msg
| SysLoginRes : str -> num -> msg
| SysPubkeyReq : msg
| SysPubkeyRes : str -> msg
| SysKeysignReq : str -> msg
| SysKeysignRes : str -> msg
| SysCreatePtyerReq : str -> msg
| SysCreatePtyerRes : fdesc -> fdesc -> msg
(* special case for errors *)
| BadTag : num -> msg.

Definition RecvMsg (c : tchan) (m : msg) : Trace :=
  match m with
| LoginReq p0 =>
RecvStr c p0 ++
RecvNum c (Num ("001", "000"))
| LoginRes p0 =>
RecvNum c p0 ++
RecvNum c (Num ("002", "000"))
| PubkeyReq  =>
(* empty payload *)
RecvNum c (Num ("003", "000"))
| PubkeyRes p0 =>
RecvStr c p0 ++
RecvNum c (Num ("004", "000"))
| KeysignReq p0 =>
RecvStr c p0 ++
RecvNum c (Num ("005", "000"))
| KeysignRes p0 =>
RecvStr c p0 ++
RecvNum c (Num ("006", "000"))
| CreatePtyerReq  =>
(* empty payload *)
RecvNum c (Num ("007", "000"))
| CreatePtyerRes p0 p1 =>
RecvFD_t c p1 ++
RecvFD_t c p0 ++
RecvNum c (Num ("008", "000"))
| SysLoginReq p0 =>
RecvStr c p0 ++
RecvNum c (Num ("009", "000"))
| SysLoginRes p0 p1 =>
RecvNum c p1 ++
RecvStr c p0 ++
RecvNum c (Num ("010", "000"))
| SysPubkeyReq  =>
(* empty payload *)
RecvNum c (Num ("011", "000"))
| SysPubkeyRes p0 =>
RecvStr c p0 ++
RecvNum c (Num ("012", "000"))
| SysKeysignReq p0 =>
RecvStr c p0 ++
RecvNum c (Num ("013", "000"))
| SysKeysignRes p0 =>
RecvStr c p0 ++
RecvNum c (Num ("014", "000"))
| SysCreatePtyerReq p0 =>
RecvStr c p0 ++
RecvNum c (Num ("015", "000"))
| SysCreatePtyerRes p0 p1 =>
RecvFD_t c p1 ++
RecvFD_t c p0 ++
RecvNum c (Num ("016", "000"))
  (* special case for errors *)
  | BadTag p0 =>
    RecvNum c p0
  end.

Definition SendMsg (c : tchan) (m : msg) : Trace :=
  match m with
| LoginReq p0 =>
SendStr c p0 ++
SendNum c (Num ("001", "000"))
| LoginRes p0 =>
SendNum c p0 ++
SendNum c (Num ("002", "000"))
| PubkeyReq  =>
(* empty payload *)
SendNum c (Num ("003", "000"))
| PubkeyRes p0 =>
SendStr c p0 ++
SendNum c (Num ("004", "000"))
| KeysignReq p0 =>
SendStr c p0 ++
SendNum c (Num ("005", "000"))
| KeysignRes p0 =>
SendStr c p0 ++
SendNum c (Num ("006", "000"))
| CreatePtyerReq  =>
(* empty payload *)
SendNum c (Num ("007", "000"))
| CreatePtyerRes p0 p1 =>
SendFD_t c p1 ++
SendFD_t c p0 ++
SendNum c (Num ("008", "000"))
| SysLoginReq p0 =>
SendStr c p0 ++
SendNum c (Num ("009", "000"))
| SysLoginRes p0 p1 =>
SendNum c p1 ++
SendStr c p0 ++
SendNum c (Num ("010", "000"))
| SysPubkeyReq  =>
(* empty payload *)
SendNum c (Num ("011", "000"))
| SysPubkeyRes p0 =>
SendStr c p0 ++
SendNum c (Num ("012", "000"))
| SysKeysignReq p0 =>
SendStr c p0 ++
SendNum c (Num ("013", "000"))
| SysKeysignRes p0 =>
SendStr c p0 ++
SendNum c (Num ("014", "000"))
| SysCreatePtyerReq p0 =>
SendStr c p0 ++
SendNum c (Num ("015", "000"))
| SysCreatePtyerRes p0 p1 =>
SendFD_t c p1 ++
SendFD_t c p0 ++
SendNum c (Num ("016", "000"))
  (* special case for errors *)
  | BadTag p0 =>
    SendNum c (Num ("000", "000"))
  end.

Definition recv_msg :
  forall (c : tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (m : msg) => tr ~~ traced (RecvMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    tag <- recv_num c tr;
    match tag with
| (Num ("001", "000")) => (* LoginReq *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("001", "000")) ++ tr);
{{ Return (LoginReq p0) }}

| (Num ("002", "000")) => (* LoginRes *)
p0 <- recv_num c
(tr ~~~ RecvNum c (Num ("002", "000")) ++ tr);
{{ Return (LoginRes p0) }}

| (Num ("003", "000")) => (* PubkeyReq *)
{{ Return (PubkeyReq ) }}

| (Num ("004", "000")) => (* PubkeyRes *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("004", "000")) ++ tr);
{{ Return (PubkeyRes p0) }}

| (Num ("005", "000")) => (* KeysignReq *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("005", "000")) ++ tr);
{{ Return (KeysignReq p0) }}

| (Num ("006", "000")) => (* KeysignRes *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("006", "000")) ++ tr);
{{ Return (KeysignRes p0) }}

| (Num ("007", "000")) => (* CreatePtyerReq *)
{{ Return (CreatePtyerReq ) }}

| (Num ("008", "000")) => (* CreatePtyerRes *)
p0 <- recv_fd c
(tr ~~~ RecvNum c (Num ("008", "000")) ++ tr);
p1 <- recv_fd c
(tr ~~~ RecvFD_t c p0 ++ RecvNum c (Num ("008", "000")) ++ tr);
{{ Return (CreatePtyerRes p0 p1) }}

| (Num ("009", "000")) => (* SysLoginReq *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("009", "000")) ++ tr);
{{ Return (SysLoginReq p0) }}

| (Num ("010", "000")) => (* SysLoginRes *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("010", "000")) ++ tr);
p1 <- recv_num c
(tr ~~~ RecvStr c p0 ++ RecvNum c (Num ("010", "000")) ++ tr);
{{ Return (SysLoginRes p0 p1) }}

| (Num ("011", "000")) => (* SysPubkeyReq *)
{{ Return (SysPubkeyReq ) }}

| (Num ("012", "000")) => (* SysPubkeyRes *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("012", "000")) ++ tr);
{{ Return (SysPubkeyRes p0) }}

| (Num ("013", "000")) => (* SysKeysignReq *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("013", "000")) ++ tr);
{{ Return (SysKeysignReq p0) }}

| (Num ("014", "000")) => (* SysKeysignRes *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("014", "000")) ++ tr);
{{ Return (SysKeysignRes p0) }}

| (Num ("015", "000")) => (* SysCreatePtyerReq *)
p0 <- recv_str c
(tr ~~~ RecvNum c (Num ("015", "000")) ++ tr);
{{ Return (SysCreatePtyerReq p0) }}

| (Num ("016", "000")) => (* SysCreatePtyerRes *)
p0 <- recv_fd c
(tr ~~~ RecvNum c (Num ("016", "000")) ++ tr);
p1 <- recv_fd c
(tr ~~~ RecvFD_t c p0 ++ RecvNum c (Num ("016", "000")) ++ tr);
{{ Return (SysCreatePtyerRes p0 p1) }}

    (* special case for errors *)
    | m =>
      {{ Return (BadTag m) }}
    end
  );
  sep fail auto;
  repeat rewrite app_ass; simpl;
  sep fail auto.
Qed.

Definition send_msg :
  forall (c : tchan) (m : msg) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    match m with
| LoginReq p0 =>
send_num c (Num ("001", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("001", "000")) ++ tr);;
{{ Return tt }}
| LoginRes p0 =>
send_num c (Num ("002", "000")) tr;;
send_num c p0
(tr ~~~ SendNum c (Num ("002", "000")) ++ tr);;
{{ Return tt }}
| PubkeyReq  =>
send_num c (Num ("003", "000")) tr;;
{{ Return tt }}
| PubkeyRes p0 =>
send_num c (Num ("004", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("004", "000")) ++ tr);;
{{ Return tt }}
| KeysignReq p0 =>
send_num c (Num ("005", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("005", "000")) ++ tr);;
{{ Return tt }}
| KeysignRes p0 =>
send_num c (Num ("006", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("006", "000")) ++ tr);;
{{ Return tt }}
| CreatePtyerReq  =>
send_num c (Num ("007", "000")) tr;;
{{ Return tt }}
| CreatePtyerRes p0 p1 =>
send_num c (Num ("008", "000")) tr;;
send_fd c p0
(tr ~~~ SendNum c (Num ("008", "000")) ++ tr);;
send_fd c p1
(tr ~~~ SendFD_t c p0 ++ SendNum c (Num ("008", "000")) ++ tr);;
{{ Return tt }}
| SysLoginReq p0 =>
send_num c (Num ("009", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("009", "000")) ++ tr);;
{{ Return tt }}
| SysLoginRes p0 p1 =>
send_num c (Num ("010", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("010", "000")) ++ tr);;
send_num c p1
(tr ~~~ SendStr c p0 ++ SendNum c (Num ("010", "000")) ++ tr);;
{{ Return tt }}
| SysPubkeyReq  =>
send_num c (Num ("011", "000")) tr;;
{{ Return tt }}
| SysPubkeyRes p0 =>
send_num c (Num ("012", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("012", "000")) ++ tr);;
{{ Return tt }}
| SysKeysignReq p0 =>
send_num c (Num ("013", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("013", "000")) ++ tr);;
{{ Return tt }}
| SysKeysignRes p0 =>
send_num c (Num ("014", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("014", "000")) ++ tr);;
{{ Return tt }}
| SysCreatePtyerReq p0 =>
send_num c (Num ("015", "000")) tr;;
send_str c p0
(tr ~~~ SendNum c (Num ("015", "000")) ++ tr);;
{{ Return tt }}
| SysCreatePtyerRes p0 p1 =>
send_num c (Num ("016", "000")) tr;;
send_fd c p0
(tr ~~~ SendNum c (Num ("016", "000")) ++ tr);;
send_fd c p1
(tr ~~~ SendFD_t c p0 ++ SendNum c (Num ("016", "000")) ++ tr);;
{{ Return tt }}
    (* special case for errors *)
    | BadTag _ =>
      send_num c (Num ("000", "000")) tr;;
      {{ Return tt }}
    end
  );
  sep fail auto;
  repeat rewrite app_ass; simpl;
  sep fail auto.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque RecvMsg SendMsg.