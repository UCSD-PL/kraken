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

Definition payload_t_of_msg (m : Msg) : payload_t :=
  match lkup_tag (tag m) as opt return OptPayloadD opt -> payload_t with
  | Some pt => fun _ : PayloadD pt => pt
  | None => fun pf : False => False_rec _ pf
  end (pay m).

Fixpoint safe_nth
  {A : Set} (l : list A) (i : nat) (pf : i < List.length l) : A.
Proof.
  refine (
    match l as l' return i < List.length l' -> A with
    | x :: xs => fun pf' : i < S (List.length xs) =>
      match i as i' return i' < S (List.length xs) -> A with
      | O => fun _ => x
      | S j => fun pf'' : S j < S (List.length xs) =>
        safe_nth A xs j (Lt.lt_S_n _ _ pf'')
      end pf'
    | nil => fun pf' : i < O =>
      _ (* bogus, use tactics *)
    end pf
  ).
  cut False; [contradiction|].
  inversion pf'.
Defined.

(* TODO clean up *)
Fixpoint get_param_idx
  (pt : payload_t) (p : PayloadD pt) (i : nat) (pf : i < List.length pt) :
  TypeD (safe_nth pt i pf).
Proof.
  refine (
    match pt as pt' return
      PayloadD pt' -> forall pf' : i < List.length pt', TypeD (safe_nth pt' i pf')
    with
    | t :: ts => fun (p : TypeD t * PayloadD ts) (pf : i < List.length (t :: ts)) =>
      match p with
      | (v, vs) =>
        match i as i' return
          forall pf' : i' < List.length (t :: ts), TypeD (safe_nth (t :: ts) i' pf')
        with
        | O => fun (pf : O < List.length (t :: ts)) => v
        | S j => fun (pf : S j < List.length (t :: ts)) =>
          get_param_idx ts vs j (Lt.lt_S_n _ _ pf)
        end pf
      end
    | nil => fun (p : unit) (pf : i < List.length nil) =>
      _ (* bogus, use tactics *)
    end p pf
  ).
  cut False; [contradiction|].
  inversion pf0.
Defined.

Lemma nth_lt_length :
  forall A (l : list A) (i : nat) (a : A),
  Some a = nth_error l i ->
  i < List.length l.
Proof.
  induction l; simpl; intros.
  destruct i; inv H.
  destruct i; inv H. omega.
  apply Lt.lt_n_S. eapply IHl; eauto.
Qed.

Section WITH_ENV.

Variable CC : fd.
Variable MSG : Msg.

Inductive base_expr : type_t -> Set :=
(* no fd lit, otherwise would make lit ctor polymorphic *)
| NLit : num -> base_expr num_t
| SLit : str -> base_expr str_t
| CurChan : base_expr fd_t
| Param :
  forall i,
  base_expr
    match lkup_tag (tag MSG) with
    | Some pt =>
      match List.nth_error pt i with
      | Some t => t
      | None => str_t
      end
    | None => str_t (* bogus *)
    end
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
  | CurChan => CC
  | Param i =>
    match lkup_tag (tag MSG) as opt return
      TypeD match opt with
      | Some pt =>
        match List.nth_error pt i with
        | Some t => t
        | None => str_t
        end
      | None => str_t
      end
    with
    | Some pt =>
      match List.nth_error pt i as ot return
        TypeD match ot with
        | Some t => t
        | None => str_t
        end
      with
      | Some t => _
      | None => _
      end
(*
      let nth := List.nth_error pt i in
      match nth as nth' return
        nth = nth' -> TypeD t
      with
      | Some t => fun pf : nth = Some t => _
      | None =>  fun pf : nth = None => _
      end (refl_equal nth)
*)
    | None => _
    end
  | UnOp t1 t2 op e =>
    let v := eval_base_expr t1 e in
    eval_unop op v
  | BinOp t1 t2 t3 op e1 e2 =>
    let v1 := eval_base_expr t1 e1 in
    let v2 := eval_base_expr t2 e2 in
    eval_binop op v1 v2
  end.





Fixpoint payload_expr (pt : payload_t) : Set :=
  match pt with
  | t::ts => base_expr t * payload_expr ts
  | nil => unit
  end%type.

Inductive expr_t : Set :=
  base_t | msg_expr_t.

Inductive expr : expr_t -> Set :=
| Base :
  forall t : type_t,
  base_expr t -> expr base_t
| MsgExpr :
  forall (tag : num) (pt : payload_t),
  Some pt = lkup_tag tag -> payload_expr pt -> expr msg_expr_t
.

Inductive cmd : Set :=
| Send : base_expr fd_t -> expr msg_expr_t -> cmd
.

Definition prog : Set :=
  list cmd.

End WITH_PAYLOAD_T.


Definition handler : Set :=
  forall m : Msg, prog (payload_t_of_msg m).

Section WITH_ENV.

Variable RC : fd.
Variable RM : Msg.
Let PT : payload_t := payload_t_of_msg RM.

Fixpoint safe_nth
  {A : Set} (l : list A) (i : nat) (pf : i < List.length l) : A.
Proof.
  refine (
    match l as l' return i < List.length l' -> A with
    | x :: xs => fun pf' : i < S (List.length xs) =>
      match i as i' return i' < S (List.length xs) -> A with
      | O => fun _ => x
      | S j => fun pf'' : S j < S (List.length xs) =>
        safe_nth A xs j (Lt.lt_S_n _ _ pf'')
      end pf'
    | nil => fun pf' : i < O =>
      _ (* bogus, use tactics *)
    end pf
  ).
  cut False; [contradiction|].
  inversion pf'.
Defined.

Fixpoint param_idx
  (pt : payload_t) (p : PayloadD pt) (i : nat) (pf : i < List.length pt) :
  TypeD (safe_nth pt i pf).
Proof.
  refine (
    match pt as pt' return
      PayloadD pt' -> forall pf' : i < List.length pt', TypeD (safe_nth pt' i pf')
    with
    | t :: ts => fun (p : TypeD t * PayloadD ts) (pf : i < List.length (t :: ts)) =>
      match p with
      | (v, vs) =>
        match i as i' return
          forall pf' : i' < List.length (t :: ts), TypeD (safe_nth (t :: ts) i' pf')
        with
        | O => fun (pf : O < List.length (t :: ts)) => v
        | S j => fun (pf : S j < List.length (t :: ts)) =>
          param_idx ts vs j (Lt.lt_S_n _ _ pf)
        end pf
      end
    | nil => fun (p : unit) (pf : i < List.length nil) =>
      _ (* bogus, use tactics *)
    end p pf
  ).
  cut False; [contradiction|].
  inversion pf0.
Qed.

Lemma nth_lt_length :
  forall A (l : list A) (i : nat) (a : A),
  Some a = nth_error l i ->
  i < List.length l.
Proof.
  induction l; simpl; intros.
  destruct i; inv H.
  destruct i; inv H. omega.
  apply Lt.lt_n_S. eapply IHl; eauto.
Qed.

Lemma lkup_tag_msg :
  forall m, exists pt, lkup_tag (tag m) = Some pt.
Proof.
  intros [tag pay]; simpl.
  destruct (lkup_tag tag); simpl in *.
  eauto. contradiction.
Qed.

Lemma payload_t_cast' :
  OptPayloadD (lkup_tag (tag RM)) = PayloadD PT.
Proof.
  revert PT; unfold payload_t_of_msg; simpl. 
  destruct (lkup_tag_msg RM).
  destruct RM as [tag pay]; simpl in *.
  revert pay; rewrite H; auto.
Qed.

(*
Lemma payload_t_cast :
  lkup_tag (tag RM) = PT.
Proof.
  revert PT; unfold payload_t_of_msg; simpl. 
  destruct (lkup_tag_msg RM).
  destruct RM as [tag pay]; simpl in *.
  revert pay; rewrite H; auto.
Qed.
*)

Variable silly : False.

Print eq_rec.

Fixpoint eval_base_expr (t : type_t) (e : base_expr PT t) : TypeD t :=
  match e in base_expr _ t return TypeD t with
  | SLit s => s
  | NLit n => n
  | CurChan => RC
  | Param i t pf =>

    match lkup_tag (tag RM) as opt return
      OptPayloadD opt -> TypeD t
    with
    | Some pt => fun p : PayloadD pt =>
      param_idx pt p i (nth_lt_length _ _ _ _ pf)
    | None => fun bogus : False =>
      False_rec _ bogus
    end (pay RM)

(*
    param_idx PT (pay RM) i (nth_lt _ _ _ _ pf)
*)

(*
      let pv : PayloadD pt := eq_rec _ _ (pay m) _ pf in
    param_idx PT (pay RM) i (nth_lt _ _ _ _ pf)
*)



(*
    match lkup_tag (tag RM) as opt return OptPayloadD opt -> TypeD t with
    | Some pt => fun p : PayloadD pt =>
      param_idx pt p i (nth_lt _ _ _ _ pf)
    | None => fun bogus : False =>
      False_rec _ bogus
    end (pay RM)
*)
  | _ => False_rec _ silly
  end.


  | Eq t' e1 e2 =>
    let v1 := eval_base_expr _ e1 in
    let v2 := eval_base_expr _ e2 in
    let cmp : forall x y : TypeD t', {x = y} + {x <> y} :=
      match t' with
      | num_t => num_eq
      | str_t => str_eq
      | fd_t  => fd_eq
      end
    in
    if cmp v1 v2 then ONE else ZERO
  | Not e =>
    let v := eval_base_expr num_t e in
    if num_eq v ZERO then ONE else ZERO
  | Add e1 e2 =>
    let v1 := eval_base_expr _ e1 in
    let v2 := eval_base_expr _ e2 in
    num_of_nat (plus (nat_of_num v1) (nat_of_num v2))
  | Sub e1 e2 =>
    let v1 := eval_base_expr _ e1 in
    let v2 := eval_base_expr _ e2 in
    num_of_nat (minus (nat_of_num v1) (nat_of_num v2))
  | Mul e1 e2 =>
    let v1 := eval_base_expr _ e1 in
    let v2 := eval_base_expr _ e2 in
    num_of_nat (mult (nat_of_num v1) (nat_of_num v2))
  | _ => False_rec _ silly
  end.

XXX


Definition CmdStep (s : kstate) (c : cmd) : kstate :=
  s.

Section WITH_HANDLER.

Variable H : handler.

Inductive Reach : kstate -> Prop :=
| Reach_init :
  forall c,
  Reach
    {| components := c :: nil
     ; ktr := [KExec  ("t" :: "e" :: "s" :: "t" :: "." :: "p" :: "y" :: nil) nil c :: nil]
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
    c <- exec (str_of_string "test.py") nil tr;
    let tr := tr ~~~ KExec (str_of_string "test.py") nil c :: nil in
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
    mm <- recv_msg c ExecPerms
    (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [In c comps] * [Reach kst] * all_bound_drop comps c);

    match mm with
    | ValidTag m =>
      let tr := tr ~~~ KRecv c m :: tr in
      send_msg c ExecPerms m
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

End WITH_MSG_T.
