Require Import List.
Require Import Ascii.
Require Import String.
Require Import NPeano.
Require Import Ynot.

Require Import ReflexBase.
Require Import ReflexIO.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.

Ltac sep' := sep fail idtac.
Ltac inv H := inversion H; subst; clear H.

Inductive type_t : Set :=
  num_t | str_t | fd_t.

Definition TypeD (t : type_t) : Set :=
  match t with
  | num_t => num
  | str_t => str
  | fd_t  => fd
  end.

Definition payload_t : Set :=
  list type_t.

Fixpoint PayloadD (pt : payload_t) : Set :=
  match pt with
  | nil => unit
  | t :: ts => TypeD t * PayloadD ts
  end%type.

Definition msg_t : Set :=
  list payload_t.

Section WITH_MSG_T.

Variable MT : msg_t.

Definition lkup_tag (n : num) :=
  List.nth_error MT (nat_of_num n).

Definition OptPayloadD (opt : option payload_t) : Set :=
  match opt with
  | Some pt => PayloadD pt
  | None => False
  end.

Record Msg : Set :=
  { tag : num
  ; pay : OptPayloadD (lkup_tag tag)
  }.

(* recv / send messages *)

Record BogusMsg : Set :=
  { btag : num
  ; bpay : lkup_tag btag = None
  }.

Inductive MaybeMsg : Set :=
| ValidTag : Msg -> MaybeMsg
| BogusTag : BogusMsg -> MaybeMsg
.

Definition RecvType (f : fd) (t : type_t) : TypeD t -> Trace :=
  match t with
  | num_t => fun n : num => RecvNum f n
  | str_t => fun s : str => RecvStr f s
  | fd_t  => fun g : fd  => RecvFD  f g :: nil
  end.

Definition SendType (f : fd) (t : type_t) : TypeD t -> Trace :=
  match t with
  | num_t => fun n : num => SendNum f n
  | str_t => fun s : str => SendStr f s
  | fd_t  => fun g : fd  => SendFD  f g :: nil
  end.

Fixpoint RecvPay (f : fd) (pt : payload_t) : PayloadD pt -> Trace :=
  match pt with
  | nil => fun _ : unit => nil
  | t :: ts => fun pv : TypeD t * PayloadD ts =>
    match pv with
    | (v, vs) => RecvPay f ts vs ++ RecvType f t v
    end
  end.

Fixpoint SendPay (f : fd) (pt : payload_t) : PayloadD pt -> Trace :=
  match pt with
  | nil => fun _ : unit => nil
  | t :: ts => fun pv : TypeD t * PayloadD ts =>
    match pv with
    | (v, vs) => SendPay f ts vs ++ SendType f t v
    end
  end.

Definition RecvOptPay (f : fd) (opt : option payload_t) : OptPayloadD opt -> Trace :=
  match opt with
  | Some pt => fun pv : PayloadD pt =>
    RecvPay f pt pv
  | None => fun pf : False =>
    False_rec Trace pf
  end.

Definition SendOptPay (f : fd) (opt : option payload_t) : OptPayloadD opt -> Trace :=
  match opt with
  | Some pt => fun pv : PayloadD pt =>
    SendPay f pt pv
  | None => fun pf : False =>
    False_rec Trace pf
  end.

Definition RecvMsg (f : fd) (m : Msg) : Trace :=
  let t := tag m in
  RecvOptPay f (lkup_tag t) (pay m) ++ RecvNum f t.

Definition RecvBogusMsg (f : fd) (m : BogusMsg) : Trace :=
  RecvNum f (btag m).

Definition SendMsg (f : fd) (m : Msg) : Trace :=
  let t := tag m in
  SendOptPay f (lkup_tag t) (pay m) ++ SendNum f t.

Definition RecvMaybeMsg (f : fd) (mm : MaybeMsg) : Trace :=
  match mm with
  | ValidTag m => RecvMsg f m
  | BogusTag bm => RecvBogusMsg f bm
  end.

Definition recv_type :
  forall (f : fd) (ps : list Perm) (t : type_t) (tr : [Trace]),
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
  forall (f : fd) (ps : list Perm) (t : type_t) (v : TypeD t) (tr : [Trace]),
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
  forall (f : fd) (ps : list Perm) (pt : payload_t) (tr : [Trace]),
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
  forall (f : fd) (ps : list Perm) (pt : payload_t) (pv : PayloadD pt) (tr : [Trace]),
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
  forall (f : fd) (ps : list Perm) (tr : [Trace]),
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
  forall (f : fd) (ps : list Perm) (m : Msg) (tr : [Trace]),
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
| KExec   : str -> list str -> fd -> KAction
| KCall   : str -> list str -> fd -> KAction
| KSelect : list fd -> fd -> KAction
| KSend   : fd -> Msg -> KAction
| KRecv   : fd -> Msg -> KAction
| KBogus  : fd -> BogusMsg -> KAction
.

Definition KTrace : Set :=
  list KAction.

Definition expand_kaction (ka : KAction) : Trace :=
  match ka with
  | KExec cmd args f => Exec cmd args f :: nil
  | KCall cmd args pipe => Call cmd args pipe :: nil
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
  mkst { components : list fd
       ; ktr : [KTrace]
       }.

Inductive unop : type_t -> type_t -> Set :=
| Not : unop num_t num_t
.

Definition eval_unop
  (t1 t2 : type_t) (op : unop t1 t2) (v : TypeD t1) : TypeD t2 :=
  match op in unop t1 t2 return TypeD t1 -> TypeD t2 with
  | Not => fun v => if num_eq v FALSE then TRUE else FALSE
  end v.

Implicit Arguments eval_unop.

Inductive binop : type_t -> type_t -> type_t -> Set :=
| Eq  : forall t, binop t t num_t
| Add : binop num_t num_t num_t
| Sub : binop num_t num_t num_t
| Mul : binop num_t num_t num_t
| Cat : binop str_t str_t str_t
.

Definition eval_binop
  (t1 t2 t3: type_t) (op : binop t1 t2 t3)
  (v1 : TypeD t1) (v2 : TypeD t2) : TypeD t3 :=
  match op in binop t1 t2 t3 return TypeD t1 -> TypeD t2 -> TypeD t3 with
  | Eq t => fun v1 v2 : TypeD t =>
    let teq : forall (x y : TypeD t), {x = y} + {x <> y} :=
      match t with
      | num_t => num_eq
      | str_t => str_eq
      | fd_t  => fd_eq
      end
    in
    if teq v1 v2 then TRUE else FALSE
  | Add => fun v1 v2 : num =>
    num_of_nat (plus (nat_of_num v1) (nat_of_num v2))
  | Sub => fun v1 v2 : num =>
    num_of_nat (minus (nat_of_num v1) (nat_of_num v2))
  | Mul => fun v1 v2 : num =>
    num_of_nat (mult (nat_of_num v1) (nat_of_num v2))
  | Cat => fun v1 v2 : str =>
    v1 ++ v2
  end v1 v2.

Implicit Arguments eval_binop.

(*

Lemma some_eq_inv :
  forall A (x y : A),
  Some x = Some y ->
  x = y.
Proof.
  intros. inv H; auto.
Qed.

Implicit Arguments some_eq_inv.

Lemma opt_eq_contra :
  forall A (a : A),
  None = Some a ->
  False.
Proof.
  intros; inv H.
Qed.

Implicit Arguments opt_eq_contra.

Fixpoint get_param_idx
  (pt : payload_t) (p : PayloadD pt) (i : nat) (t : type_t)
  (pf : List.nth_error pt i = Some t) : TypeD t :=
  match pt as pt' return
    PayloadD pt' -> forall pf : List.nth_error pt' i = Some t, TypeD t
  with
  | x :: xs =>
    fun (p : TypeD x * PayloadD xs) (pf : List.nth_error (x :: xs) i = Some t) =>
    match p with
    | (v, vs) =>
      match i as i' return
        forall pf : List.nth_error (x :: xs) i' = Some t, TypeD t
      with
      | O => fun pf : Some x = Some t =>
        eq_rec _ _ v _ (some_eq_inv pf)
      | S j => fun pf : List.nth_error xs j = Some t =>
        get_param_idx xs vs j t pf
      end pf
    end
  | nil =>
    fun (p : unit) (pf : List.nth_error nil i = Some t) =>
    match i as i' return List.nth_error nil i' = Some t -> _ with
    | O => fun pf : None = Some t => False_rec _ (opt_eq_contra pf)
    | S _ => fun pf : None = Some t => False_rec _ (opt_eq_contra pf)
    end pf
  end p pf.

*)

Definition optpayload_get_t (opt : option payload_t) (i : nat) : type_t :=
  match opt with
  | Some pt => List.nth i pt str_t
  | None => str_t
  end.

Fixpoint payload_get_v
  (i : nat) (pt : payload_t) (p : PayloadD pt) : TypeD (List.nth i pt str_t) :=
  match i as i' return TypeD (List.nth i' pt str_t) with
  | S j =>
    match pt as pt' return
      PayloadD pt' -> TypeD (List.nth (S j) pt' str_t)
    with
    | t :: ts => fun p =>
      match p with (v, vs) => payload_get_v j ts vs end
    | nil => fun _ =>
      str_of_string "BOGUS"
    end p
  | O =>
    match pt as pt' return
      PayloadD pt' -> TypeD (List.nth O pt' str_t)
    with
    | t :: ts => fun p =>
      match p with (v, vs) => v end
    | nil => fun _ =>
      str_of_string "BOGUS"
    end p
  end.

Section WITH_ENV.

Variable CST : kstate.
Variable CFD : fd.
Variable CMSG : Msg.

Let CPAY := lkup_tag (tag CMSG).

Definition mparam_i (i : nat) : TypeD (optpayload_get_t CPAY i) :=
  match CPAY as opt return
    OptPayloadD opt -> TypeD (optpayload_get_t opt i)
  with
  | Some pt => fun p : PayloadD pt => payload_get_v i pt p
  | None => fun pf : False => False_rec _ pf
  end (pay CMSG).

Inductive base_expr : type_t -> Set :=
(* no fd lit, otherwise would make lit ctor polymorphic *)
| NLit : num -> base_expr num_t
| SLit : str -> base_expr str_t
| CurChan : base_expr fd_t
| Param :
  forall i,
  base_expr (optpayload_get_t CPAY i)
| UnOp :
  forall t1 t2,
  unop t1 t2 ->
  base_expr t1 ->
  base_expr t2
| BinOp :
  forall t1 t2 t3,
  binop t1 t2 t3 ->
  base_expr t1 ->
  base_expr t2 ->
  base_expr t3
.

Fixpoint eval_base_expr (t : type_t) (e : base_expr t) : TypeD t :=
  match e in base_expr t return TypeD t with
  | NLit n => n
  | SLit s => s
  | CurChan => CFD
  | Param i => mparam_i i
  | UnOp t1 t2 op e =>
    let v := eval_base_expr t1 e in
    eval_unop op v
  | BinOp t1 t2 t3 op e1 e2 =>
    let v1 := eval_base_expr t1 e1 in
    let v2 := eval_base_expr t2 e2 in
    eval_binop op v1 v2
  end.

Definition msg_fds_ok : Prop :=
  forall i,
  let t := optpayload_get_t CPAY i in
  match t as t' return TypeD t' -> Prop with
  | fd_t => fun f => In f (components CST)
  | _ => fun _ => True
  end (mparam_i i).

(* this extracts to not-the-worst code, not tail recursive *)
Definition mem
  {A : Type} (deq : forall x y : A, {x = y} + {x <> y}) (xs : list A) (x : A) :
  {In x xs} + {~ In x xs}.
Proof.
  induction xs; simpl; auto.
  destruct IHxs; auto.
  destruct (deq a x); subst; auto.
  right; intro. destruct H; auto.
Qed.

(* really need to generalize all this payload business *)
(* this should be some sort of a forallb type function *)
Fixpoint pay_fds_ck
  (fs : list fd) (pt : payload_t) (p : PayloadD pt) : bool :=
  match pt as pt' return
    PayloadD pt' -> bool
  with
  | nil => fun _ : unit => true
  | t::ts => fun p : (TypeD t * PayloadD ts) =>
    match p with (v, vs) =>
      andb
        (match t as t' return TypeD t' -> bool with
        | fd_t => fun f => if mem fd_eq fs f then true else false
        | _ => fun _ => true
        end v)
        (pay_fds_ck fs ts vs)
    end
  end p.

Definition msg_fds_ck : bool :=
  match lkup_tag (tag CMSG) as opt return OptPayloadD opt -> bool with
  | Some pt => fun p : PayloadD pt =>
    pay_fds_ck (components CST) pt p
  | None => fun pf : False =>
    False_rec _ pf
  end (pay CMSG).

(* TODO fix this, it is ugly and stupid *)
Lemma msg_fds_ck_correct :
  msg_fds_ck = true <-> msg_fds_ok.
Proof.
  destruct CST as [fs tr].
  unfold msg_fds_ck, msg_fds_ok.
  unfold mparam_i, optpayload_get_t.
  unfold CPAY in *; clear CPAY.
  destruct CMSG as [mtag mpay]; simpl.
  split.

  (* -> *)

  revert mpay.
  destruct (lkup_tag mtag); simpl; intros; auto.
  clear tr mtag.
  revert p mpay H.
  induction i; simpl; intros.

  destruct p; simpl in *; auto.
  destruct mpay; simpl in *; auto.
  destruct t; simpl in *; auto.
  destruct (mem fd_eq (components CST) t0); auto.
  discriminate.

  destruct p; simpl in *; auto.
  destruct mpay; simpl in *; auto.
  apply IHi.
  destruct t; simpl in H; auto.
  destruct (mem fd_eq (components CST) t0); auto.
  discriminate.

  (* <- *)  

  revert mpay.
  destruct (lkup_tag mtag); simpl; intros; auto.
  clear tr mtag.
  revert p mpay H.
  induction p; simpl; intros.

  auto.

  destruct mpay; simpl in *.
  destruct a; simpl in *; auto.
  apply IHp; intros. specialize (H (S i)); auto.
  apply IHp; intros. specialize (H (S i)); auto.
  destruct (mem fd_eq (components CST) t) as [X|X]; simpl.
  apply IHp; intros. specialize (H (S i)); auto.
  destruct X. apply (H O).
Qed.

Lemma base_expr_fd_in :
  forall t e v,
  msg_fds_ok ->
  In CFD (components CST)->
  eval_base_expr t e = v ->
  match t as t' return (TypeD t' -> Prop) with
  | fd_t => fun f => In f (components CST)
  | _ => fun _ => True
  end v.
Proof.
  destruct e; simpl; intros; subst; auto.
  specialize (H i); auto.
  destruct t2; auto. inv u.
  destruct t3; auto. inv b.
Qed.

Fixpoint payload_expr (pt : payload_t) : Set :=
  match pt with
  | t::ts => base_expr t * payload_expr ts
  | nil => unit
  end%type.

Fixpoint eval_payload_expr (pt : payload_t) (e : payload_expr pt) : PayloadD pt :=
 match pt as pt' return payload_expr pt' -> PayloadD pt' with
 | t :: ts => fun e : base_expr t * payload_expr ts =>
   match e with
   | (e1, es) =>
     let v1 := eval_base_expr t e1 in
     let vs := eval_payload_expr ts es in
     (v1, vs)
   end
 | nil => fun _ => tt
 end e.

Inductive expr_t : Set :=
| base_t : type_t -> expr_t
| msg_expr_t : expr_t
.

Definition ExprTD (t : expr_t) : Set :=
  match t with
  | base_t t => TypeD t
  | msg_expr_t => Msg
  end.

Inductive expr : expr_t -> Set :=
| Base :
  forall t : type_t,
  base_expr t ->
  expr (base_t t)
| MsgExpr :
  forall (tag : num) (pt : payload_t),
  Some pt = lkup_tag tag ->
  payload_expr pt ->
  expr msg_expr_t
.

Definition eval_expr (t : expr_t) (e : expr t) : ExprTD t :=
  match e in expr t return ExprTD t with
  | Base t e => eval_base_expr t e
  | MsgExpr tag pt pf pe =>
    let p : PayloadD pt := eval_payload_expr pt pe in
    let p : OptPayloadD (lkup_tag tag) :=
      eq_rec (Some pt) (fun e : option payload_t => OptPayloadD e) p (lkup_tag tag) pf
    in
    {| tag := tag; pay := p |}
  end.

Inductive cmd : Set :=
| Send : base_expr fd_t -> expr msg_expr_t -> cmd
.

Definition RunCmd (s : kstate) (c : cmd) : kstate :=
  match c with
  | Send fe me =>
    let f := eval_base_expr _ fe in
    let m := eval_expr _ me in
    let tr := ktr s in
    {| components := components s
     ; ktr := tr ~~~ KSend f m :: tr
     |}
  end.
  
Definition prog : Set :=
  list cmd.

Fixpoint RunProg (s : kstate) (p : prog) : kstate :=
  match p with
  | c :: cs => RunProg (RunCmd s c) cs
  | nil => s
  end.

End WITH_ENV.

Definition handler : Set :=
  forall m : Msg, prog m.

Section WITH_HANDLER.

Variable HANDLER : handler.

Inductive Reach : kstate -> Prop :=
| Reach_init :
  forall f,
  Reach
    {| components := f :: nil
     ; ktr := [KExec  ("t" :: "e" :: "s" :: "t" :: "." :: "p" :: "y" :: nil) nil f :: nil]
     |}
| Reach_valid :
  forall s f m tr s',
  msg_fds_ok s m ->
  let cs := components s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  s' = {| components := cs
        ; ktr := [KRecv f m :: KSelect cs f :: tr]
        |} ->
  Reach (RunProg f m s' (HANDLER m))
| Reach_bad_fds :
  forall s f m tr,
  ~ msg_fds_ok s m ->
  let cs := components s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  Reach
    {| components := cs
     ; ktr := [KRecv f m :: KSelect cs f :: tr]
     |}
| Reach_bogus :
  forall s f bmsg tr,
  let cs := components s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  Reach
    {| components := cs
     ; ktr := [KBogus f bmsg :: KSelect cs f :: tr]
     |}
.

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
  | [ H: ?tr = [_]%inhabited |- context[inhabit_unpack ?tr _] ] =>
    rewrite H; simpl
  | [ H: ktr ?s = [_]%inhabited |- _ ] =>
    unfold s in *; simpl in *
  | [ H1 : ktr ?s = [_]%inhabited, H2 : ktr ?s = [_]%inhabited |- _ ] =>
    rewrite H1 in H2; apply pack_injective in H2;
    rewrite -> H2 in * || rewrite <- H2 in * (* subst may be blocked *)
  end.

Ltac misc :=
  match goal with
  | [ |- Reach _ ] =>
      econstructor; eauto
  | [ H : msg_fds_ck _ ?m = true |- msg_fds_ok _ ?m ] =>
    apply msg_fds_ck_correct; auto
  | [ H1 : msg_fds_ck _ ?m = false, H2 : msg_fds_ok _ ?m |- False ] =>
    apply msg_fds_ck_correct in H2; congruence
  end.

Ltac unfoldr :=
  unfold kstate_inv.

Ltac simplr :=
  sep';
  try uninhabit;
  try bounds_packing;
  try misc.

Ltac sep'' :=
  sep unfoldr simplr.

Definition kinit :
  forall (_ : unit),
  STsep (traced nil)
        (fun s => kstate_inv s).
Proof.
  intros; refine (
    let tr := [nil]%inhabited in
    c <- exec (str_of_string "test.py") nil tr;
    let tr := tr ~~~ KExec (str_of_string "test.py") nil c :: nil in
    {{Return {|components := c :: nil; ktr := tr|}}}
  );
  sep''.
Qed.

Definition run_cmd :
  forall (cfd : fd) (cm : Msg) (s : kstate) (c : cmd cm),
  STsep (tr :~~ ktr s in
          traced (expand_ktrace tr) * all_bound (components s) *
          [In cfd (components s)] * [msg_fds_ok s cm])
        (fun s' : kstate => tr :~~ ktr s' in
          traced (expand_ktrace tr) * all_bound (components s') *
          [In cfd (components s')] * [msg_fds_ok s' cm] * [RunCmd cfd cm s c = s']).
Proof.
  intros; refine (
    let comps := components s in
    let tr := ktr s in
    match c with
    | Send fe me =>
      let f := eval_base_expr cfd cm _ fe in
      let m := eval_expr cfd cm _ me in
      send_msg f ExecPerms m
      (tr ~~~ expand_ktrace tr)
      <@> all_bound_drop comps f * [In cfd comps] * [msg_fds_ok s cm];;

      let tr := tr ~~~ KSend f m :: tr in
      {{Return {|components := comps; ktr := tr|}}}
    end
  );
  sep''.
  eapply (base_expr_fd_in s cfd cm fd_t); eauto.
  eapply (base_expr_fd_in s cfd cm fd_t); eauto.
Qed.

Definition run_prog :
  forall (cfd : fd) (cm : Msg) (s : kstate) (p : prog cm),
  STsep (tr :~~ ktr s in
          traced (expand_ktrace tr) * all_bound (components s) *
          [In cfd (components s)] * [msg_fds_ok s cm])
        (fun s' : kstate => tr :~~ ktr s' in
          traced (expand_ktrace tr) * all_bound (components s') *
          [In cfd (components s')] * [msg_fds_ok s' cm] * [RunProg cfd cm s p = s']).
Proof.
  intros; refine (
    Fix2
      (fun p s =>
        tr :~~ ktr s in
          traced (expand_ktrace tr) * all_bound (components s) *
          [In cfd (components s)] * [msg_fds_ok s cm])
      (fun p s (s' : kstate) =>
        tr :~~ ktr s' in
          traced (expand_ktrace tr) * all_bound (components s') *
          [In cfd (components s')] * [msg_fds_ok s' cm] * [RunProg cfd cm s p = s'])
      (fun self p s =>
        match p with
        | nil =>
          {{ Return s }}
        | c::cs =>
          s' <- run_cmd cfd cm s c;
          s'' <- self cs s' <@> [RunCmd cfd cm s c = s'];
          {{ Return s'' }}
        end)
    p s
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
    mm <- recv_msg c ExecPerms
    (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [In c comps] * [Reach kst] * all_bound_drop comps c);

    match mm with
    | ValidTag m =>
      let tr := tr ~~~ KRecv c m :: tr in
      let ck := msg_fds_ck kst m in
      match ck as ck' return ck = ck' -> _ with
      | true => fun _ =>
        let s' := {|components := comps; ktr := tr|} in
        s'' <- run_prog c m s' (HANDLER m) <@> [Reach kst];
        {{Return s''}}
      | false => fun _ =>
        {{Return {|components := comps; ktr := tr|}}}
      end (refl_equal ck)

    | BogusTag m =>
      let tr := tr ~~~ KBogus c m :: tr in
      {{Return {|components := comps; ktr := tr|}}}
    end
  );
  sep''.
  subst v; sep''.

  econstructor; eauto.
  unfold s' in *; rewrite <- H6.
  eapply (Reach_valid kst); eauto.
  apply msg_fds_ck_correct; auto.
  f_equal; auto. sep''.
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

End WITH_HANDLER.

End WITH_MSG_T.