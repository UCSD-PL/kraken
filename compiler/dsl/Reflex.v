Require Import List.
Require Import Ascii.
Require Import String.
Require Import NPeano.
Require Import Ynot.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.

Ltac sep' := sep fail idtac.
Ltac inv H := inversion H; subst; clear H.

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
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque nat_of_Num Num_of_nat Num_eq.

Definition Str : Set :=
  list ascii.

Fixpoint str_of_string (s : string) : Str :=
  match s with
  | EmptyString => nil
  | String c rest => c :: str_of_string rest
  end.

Definition FD : Set :=
  Num.

Definition FD_eq (f1 f2 : FD) : {f1 = f2} + {f1 <> f2} :=
  Num_eq f1 f2.

Lemma FD_eq_true :
  forall (f : FD) (A : Type) (vT vF : A),
  (if FD_eq f f then vT else vF) = vT.
Proof.
  intros; case (FD_eq f f); auto. congruence.
Qed.

Lemma FD_eq_false :
  forall (f1 f2 : FD) (A : Type) (vT vF : A),
  f1 <> f2 ->
  (if FD_eq f1 f2 then vT else vF) = vF.
Proof.
  intros; case (FD_eq f1 f2); auto. congruence.
Qed.

Inductive Action : Set :=
| Exec   : Str -> FD -> Action
| Call   : Str -> Str -> FD -> Action
| Select : list FD -> FD -> Action
| Recv   : FD -> Str -> Action
| Send   : FD -> Str -> Action
| RecvFD : FD -> FD -> Action (* RecvFD f f' : use f to recv f' *)
| SendFD : FD -> FD -> Action (* SendFD f f' : use f to send f' *)
.

Definition Trace : Set := list Action.

Axiom traced : Trace -> hprop.

Inductive Perm : Set :=
  RecvP | SendP | RecvFDP | SendFDP.

Definition CompPerms : list Perm :=
  RecvP :: SendP :: RecvFDP :: SendFDP :: nil.

Definition CallPerms : list Perm :=
  RecvP :: RecvFDP :: nil.

Axiom open : FD -> list Perm -> hprop.

Axiom exec :
  forall (prog : Str) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun f : FD => tr ~~ open f CompPerms * traced (Exec prog f :: tr)).

Axiom call :
  forall (prog arg : Str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun f : FD => tr ~~ open f CallPerms * traced (Call prog arg f :: tr)).

(* TODO add non-empty precondition *)
(* TODO add open w/ recv perms precondition *)
Axiom select :
  forall (fs : list FD) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun f : FD => tr ~~ traced (Select fs f :: tr) * [In f fs]).

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
  sep'; discriminate.
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
  sep'.
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
  sep'.
  rewrite <- H.
  rewrite Num_nat_embedding.
  sep'.
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
  sep'.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque RecvNum SendNum RecvStr SendStr.

Section MESSAGE_SPEC.

Variable MS : msg_spec.

Definition lkup_tag (n : Num) :=
  List.nth_error MS (nat_of_Num n).

Definition TypeD (t : type_t) : Set :=
  match t with
  | num_t => Num
  | str_t => Str
  | fd_t  => FD
  end.

Fixpoint PayloadD (pt : payload_t) : Set :=
  match pt with
  | nil => unit
  | t :: ts => TypeD t * PayloadD ts
  end%type.

Definition OptPayloadD (opt : option payload_t) : Set :=
  match opt with
  | Some pt => PayloadD pt
  | None => False
  end.

Record Msg : Set :=
  { tag : Num
  ; pay : OptPayloadD (lkup_tag tag)
  }.

Record BogusMsg : Set :=
  { btag : Num
  ; bpay : lkup_tag btag = None
  }.

Inductive MaybeMsg : Set :=
| ValidTag : Msg -> MaybeMsg
| BogusTag : BogusMsg -> MaybeMsg
.

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
  | nil => fun _ : unit => nil
  | t :: ts => fun pv : TypeD t * PayloadD ts =>
    match pv with
    | (v, vs) => RecvPay f ts vs ++ RecvType f t v
    end
  end.

Fixpoint SendPay (f : FD) (pt : payload_t) : PayloadD pt -> Trace :=
  match pt with
  | nil => fun _ : unit => nil
  | t :: ts => fun pv : TypeD t * PayloadD ts =>
    match pv with
    | (v, vs) => SendPay f ts vs ++ SendType f t v
    end
  end.

Definition RecvOptPay (f : FD) (opt : option payload_t) : OptPayloadD opt -> Trace :=
  match opt with
  | Some pt => fun pv : PayloadD pt =>
    RecvPay f pt pv
  | None => fun pf : False =>
    False_rec Trace pf
  end.

Definition SendOptPay (f : FD) (opt : option payload_t) : OptPayloadD opt -> Trace :=
  match opt with
  | Some pt => fun pv : PayloadD pt =>
    SendPay f pt pv
  | None => fun pf : False =>
    False_rec Trace pf
  end.

Definition RecvMsg (f : FD) (m : Msg) : Trace :=
  let t := tag m in
  RecvOptPay f (lkup_tag t) (pay m) ++ RecvNum f t.

Definition RecvBogusMsg (f : FD) (m : BogusMsg) : Trace :=
  RecvNum f (btag m).

Definition SendMsg (f : FD) (m : Msg) : Trace :=
  let t := tag m in
  SendOptPay f (lkup_tag t) (pay m) ++ SendNum f t.

Definition RecvMaybeMsg (f : FD) (mm : MaybeMsg) : Trace :=
  match mm with
  | ValidTag m => RecvMsg f m
  | BogusTag bm => RecvBogusMsg f bm
  end.

Definition recv_type :
  forall (f : FD) (ps : list Perm) (t : type_t) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
        (fun v : TypeD t => tr ~~ traced (RecvType f t v ++ tr) * open f ps).
Proof.
  intros; refine (
    match t as t' return STsep _ (fun v : TypeD t' => _) with
    | num_t =>
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
  sep'.
Qed.

Definition send_type :
  forall (f : FD) (ps : list Perm) (t : type_t) (v : TypeD t) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
        (fun _ : unit => tr ~~ traced (SendType f t v ++ tr) * open f ps).
Proof.
  intros; refine (
    match t as t' return
      forall v: TypeD t',
      STsep _ (fun _ => tr ~~ traced (SendType f t' v ++ tr) * _)
    with
    | num_t => fun v =>
      send_num f ps v tr;;
      {{ Return tt }}
    | str_t => fun v =>
      send_str f ps v tr;;
      {{ Return tt }}
    | fd_t => fun v =>
      send_fd f ps v tr;;
      {{ Return tt }}
    end v
  );
  sep'.
Qed.

Definition recv_pay :
  forall (f : FD) (ps : list Perm) (pt : payload_t) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
        (fun pv : PayloadD pt => tr ~~ traced (RecvPay f pt pv ++ tr) * open f ps).
Proof.
  intros; refine (
    Fix2
      (fun pt tr => tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
      (fun pt tr (pv : PayloadD pt) => tr ~~ traced (RecvPay f pt pv ++ tr) * open f ps)
      (fun self pt tr =>
        match pt as pt' return STsep _ (fun x : PayloadD pt' => _) with
        | nil =>
          {{ Return tt }}
        | t::ts =>
          v  <- recv_type f ps t tr <@> [In RecvP ps] * [In RecvFDP ps];
          vs <- self ts (tr ~~~ RecvType f t v ++ tr);
          {{ Return (v, vs) }}
        end)
    pt tr
  );
  sep'.
  inv H; rewrite app_assoc; sep'.
Qed.

Definition send_pay :
  forall (f : FD) (ps : list Perm) (pt : payload_t) (pv : PayloadD pt) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
        (fun _ : unit => tr ~~ traced (SendPay f pt pv ++ tr) * open f ps).
Proof.
  intros; refine (
    Fix3
      (fun pt pv tr => tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
      (fun pt pv tr _ => tr ~~ traced (SendPay f pt pv ++ tr) * open f ps)
      (fun self pt pv tr =>
        match pt as pt' return
          forall pv : PayloadD pt',
          STsep _ (fun _ => tr ~~ traced (SendPay f pt' pv ++ tr) * _)
        with
        | nil => fun _ : unit =>
          {{ Return tt }}
        | t::ts => fun pv : TypeD t * PayloadD ts =>
          match pv with
          | (v, vs) =>
            send_type f ps t v tr <@> [In SendP ps] * [In SendFDP ps];;
            self ts vs (tr ~~~ SendType f t v ++ tr);;
            {{ Return tt }}
          end
        end pv)
    pt pv tr
  );
  sep'.
  rewrite app_assoc; sep'.
Qed.

Definition recv_msg :
  forall (f : FD) (ps : list Perm) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
        (fun mm : MaybeMsg => tr ~~ traced (RecvMaybeMsg f mm ++ tr) * open f ps).
Proof.
  intros; refine (
    t <- recv_num f ps tr <@> [In RecvP ps] * [In RecvFDP ps];
    let opt := lkup_tag t in
    match opt as opt' return opt = opt' -> _ with
    | Some pt => fun pf : opt = Some pt =>
      pv <- recv_pay f ps pt (tr ~~~ RecvNum f t ++ tr);
      let pv' : OptPayloadD opt :=
        eq_rec_r (x := Some pt) OptPayloadD pv pf
      in
      {{ Return (ValidTag (Build_Msg t pv')) }}
    | None => fun pf : opt = None =>
      {{ Return (BogusTag (Build_BogusMsg t pf)) }}
    end (refl_equal _)
  );
  sep'.
  unfold RecvMsg, pv', eq_rec_r; simpl.
  rewrite pf; simpl.
  rewrite app_assoc; sep'.
Qed.

Definition send_msg :
  forall (f : FD) (ps : list Perm) (m : Msg) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
        (fun _ : unit => tr ~~ traced (SendMsg f m ++ tr) * open f ps).
Proof.
  intros; refine (
    let t := tag m in
    let opt := lkup_tag t in
    match opt as opt' return opt = opt' -> _ with
    | Some pt => fun pf : opt = Some pt =>
      let pv : PayloadD pt := eq_rec _ _ (pay m) _ pf in
      send_num f ps t tr <@> [In SendP ps] * [In SendFDP ps];;
      send_pay f ps pt pv (tr ~~~ SendNum f t ++ tr);;
      {{ Return tt }}
    | None => fun pf : opt = None =>
      let x : False := eq_rec _ _ (pay m) _ pf in
      False_rec _ x
    end (refl_equal opt)
  );
  sep'.
  unfold SendMsg, t, pv in *; clear t pv.
  destruct m as [P T]; simpl in *.
  revert T; rewrite pf; simpl; intro T.
  rewrite app_assoc; sep'.
Qed.

Inductive KAction : Set :=
| KExec   : Str -> FD -> KAction
| KCall   : Str -> Str -> FD -> KAction
| KSelect : list FD -> FD -> KAction
| KSend   : FD -> Msg -> KAction
| KRecv   : FD -> Msg -> KAction
| KBogus  : FD -> BogusMsg -> KAction
.

Definition KTrace : Set :=
  list KAction.

Definition expand_kaction (ka : KAction) : Trace :=
  match ka with
  | KExec cmd f => Exec cmd f :: nil
  | KCall cmd arg pipe => Call cmd arg pipe :: nil
  | KSelect cs f => Select cs f :: nil
  | KSend f m => SendMsg f m
  | KRecv f m => RecvMsg f m
  | KBogus f bm => RecvBogusMsg f bm
  end.

Fixpoint expand_ktrace (kt : KTrace) : Trace :=
  match kt with
  | nil => nil
  | ka :: kas => expand_kaction ka ++ expand_ktrace kas
  end.

Record kstate : Set :=
  mkst { components : list FD
       ; ktr : [KTrace]
       }.

Inductive Reach : kstate -> Prop :=
| Reach_init :
  forall c,
  Reach
    {| components := c :: nil
     ; ktr := [KExec  ("t" :: "e" :: "s" :: "t" :: "." :: "p" :: "y" :: nil) c :: nil]
     |}
| Reach_valid :
  forall s c msg tr,
  let cs := components s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  Reach
    {| components := cs
     ; ktr := [KSend c msg :: KRecv c msg :: KSelect cs c :: tr]
     |}
| Reach_bogus :
  forall s c bmsg tr,
  let cs := components s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  Reach
    {| components := cs
     ; ktr := [KBogus c bmsg :: KSelect cs c :: tr]
     |}
.

Definition bound (f : FD) : hprop :=
  open f CompPerms.

Fixpoint all_bound (fds : list FD) : hprop :=
  match fds with
  | nil => emp
  | f :: fs => bound f * all_bound fs
  end.

Fixpoint all_bound_drop (fds : list FD) (drop : FD) : hprop :=
  match fds with
  | nil => emp
  | f :: fs =>
    if FD_eq f drop
      then all_bound fs
      else open f CompPerms * all_bound_drop fs drop
  end.

Lemma unpack_all_bound :
  forall fs f,
  In f fs ->
  all_bound fs ==> bound f * all_bound_drop fs f.
Proof.
  induction fs; simpl; intros. contradiction.
  destruct H; subst. rewrite FD_eq_true. apply himp_refl.
  case (FD_eq a f); intros; subst. apply himp_refl.
  apply himp_comm_conc. apply himp_assoc_conc1.
  apply himp_split. apply himp_refl.
  apply himp_comm_conc; auto.
Qed.

Lemma repack_all_bound :
  forall fs f,
  In f fs ->
  bound f * all_bound_drop fs f ==> all_bound fs.
Proof.
  induction fs; simpl; intros. contradiction.
  destruct H; subst. rewrite FD_eq_true. apply himp_refl.
  case (FD_eq a f); intros; subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Definition kstate_inv s : hprop :=
  tr :~~ ktr s in emp
  * traced (expand_ktrace tr)
  * [Reach s]
  * all_bound (components s)
  .

Ltac isolate t :=
  match t with ?lhs ==> ?rhs =>
    refine (@himp_trans (lhs * _) _ _ _ _); [ sep' | ];
    refine (@himp_trans (rhs * _) _ _ _ _); [ | sep' ];
    apply himp_split
  end.

Ltac bounds_packing :=
  match goal with
  | [ |- ?lhs ==> ?rhs ] =>
    match lhs with context [ all_bound_drop ?cs ?c ] =>
      isolate (bound c * all_bound_drop cs c ==> all_bound cs);
      [ apply repack_all_bound | ]
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match rhs with context [ all_bound_drop ?cs ?c ] =>
      isolate (all_bound cs ==> bound c * all_bound_drop cs c);
      [ apply unpack_all_bound | ]
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match lhs with context [ all_bound_drop ?cs ?c ] =>
    match rhs with context [ all_bound_drop ?cs ?d ] =>
      isolate (bound c * all_bound_drop cs c ==> bound d * all_bound_drop cs d);
      [ eapply himp_trans; [ apply repack_all_bound | apply unpack_all_bound ] | ]
    end
    end
end.

Ltac uninhabit :=
  match goal with
  | [ H1: ?tr = [_]%inhabited, H2: context[inhabit_unpack ?tr _] |- _ ] =>
    rewrite H1 in H2; simpl in H2
  | [ H: ?tr = [_]%inhabited |- context[inhabit_unpack ?tr _]] =>
    rewrite H; simpl
  end.

Ltac reach :=
  match goal with
  | [ |- Reach _ ] =>
      econstructor; eauto
  end.

Ltac unfoldr :=
  unfold kstate_inv.

Ltac simplr :=
  sep';
  try uninhabit;
  try bounds_packing;
  try reach.

Ltac sep'' :=
  sep unfoldr simplr.

Definition kinit :
  forall (_ : unit),
  STsep (traced nil)
        (fun s => kstate_inv s).
Proof.
  intros; refine (
    let tr := [nil]%inhabited in
    c <- exec (str_of_string "test.py") tr;
    let tr := tr ~~~ KExec (str_of_string "test.py") c :: nil in
    {{Return {|components := c :: nil; ktr := tr|}}}
  );
  sep''.
Qed.

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  intro kst.
  remember (components kst) as comps.
  refine (
    let tr := ktr kst in
    c <- select comps
    (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [Reach kst] * all_bound comps);

    let tr := tr ~~~ KSelect comps c :: tr in
    mm <- recv_msg c CompPerms
    (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [In c comps] * [Reach kst] * all_bound_drop comps c);

    match mm with
    | ValidTag m =>
      let tr := tr ~~~ KRecv c m :: tr in
      send_msg c CompPerms m
      (tr ~~~ expand_ktrace tr)
      <@> (tr ~~ [In c comps] * [Reach kst] * all_bound_drop comps c);;

      let tr := tr ~~~ KSend c m :: tr in
      {{Return {|components := comps; ktr := tr|}}}

    | BogusTag m =>
      let tr := tr ~~~ KBogus c m :: tr in
      {{Return {|components := comps; ktr := tr|}}}
    end
  );
  sep''.
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
  sep'.
Qed.

Definition main:
  forall (_ : unit),
  STsep (traced nil)
        (fun s' => kstate_inv s').
Proof.
  intros; refine (
    s0 <- kinit tt;
    sN <- kloop s0;
    {{ Return sN }}
  );
  sep'.
Qed.

End MESSAGE_SPEC.