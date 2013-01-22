Require Import List.
Require Import Ascii.
Require Import String.
Require Import NPeano.
Require Import Ynot.

Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexIO.
Require Import ReflexVec.
Require Import ReflexHVec.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.
Open Scope list_scope.

Ltac sep' := sep fail idtac.
Ltac inv H := inversion H; subst; clear H.

Inductive desc : Set := num_d | str_d | fd_d.

Definition denote_desc (d : desc) : Type :=
  match d with
  | num_d => num
  | str_d => str
  | fd_d  => fd
  end
.

Instance Denoted_desc : Denoted desc :=
{ denote := denote_desc
}.

Definition payload_desc' n : Type := vec desc n.

Definition denote_payload_desc' n (pt : payload_desc' n) : Type :=
  hvec pt.

Instance Denoted_payload_desc' { n } : Denoted (payload_desc' n) :=
{ denote := denote_payload_desc' n
}.

(* Thank you Ynot for breaking sigT notation... *)
Definition payload_desc := (sigT (fun (n : nat) => payload_desc' n)).

Instance Denoted_payload_desc : Denoted payload_desc :=
{ denote := fun pd => @denote _ (@Denoted_payload_desc' (projT1 pd)) (projT2 pd)
}.

Definition payload_desc_vec n := vec payload_desc n.

Section WITH_PAYLOAD_DESC_VEC.

Variable NB_MSG : nat.
Variable PDV : payload_desc_vec NB_MSG.

Definition lkup_tag (tag : fin NB_MSG) : payload_desc :=
  v_get PDV tag.

Record msg : Type :=
  { tag : fin NB_MSG
  ; pay : [[ lkup_tag tag ]]
  }.

Definition trace_recv (f : fd) (d : desc) : [[ d ]] -> Trace :=
  match d with
  | num_d => fun n : num => RecvNum f n
  | str_d => fun s : str => RecvStr f s
  | fd_d  => fun g : fd  => RecvFD  f g :: nil
  end.

Definition trace_send (f : fd) (d : desc) : [[ d ]] -> Trace :=
  match d with
  | num_d => fun n : num => SendNum f n
  | str_d => fun s : str => SendStr f s
  | fd_d  => fun g : fd  => SendFD  f g :: nil
  end.

Record bogus_msg : Set :=
  { btag : num
  ; bbad : nat_of_num btag >= NB_MSG
  }.

Definition maybe_msg := (msg + bogus_msg)%type.

Section WITH_TRACE_FUN.

Variable trace_fun : fd -> forall (d : desc), [[ d ]] -> list Action.

Fixpoint trace_payload_desc'
  (n : nat) (pd : payload_desc' n) (f : fd) (p : [[ pd ]]) : Trace :=
  match n as _n return
    forall (pd : payload_desc' _n) (p : [[ pd ]]), Trace
  with
  | O => fun _ _ => nil
  | S n' => fun (pd : payload_desc' (S n')) (p : [[ pd ]]) =>
    match pd as _pd return
      forall (p : @denote _ (@Denoted_payload_desc' (S n')) _pd), Trace
    with
    | (d, pd') => fun p => trace_payload_desc' n' pd' f (snd p) ++ trace_fun f d (fst p)
    end p
  end pd p
.

Definition trace_payload_desc (pd : payload_desc) :=
  trace_payload_desc' (projT1 pd) (projT2 pd).

Definition trace_opt_payload_desc (opd : option payload_desc) (f : fd)
  : [! opd !] -> Trace :=
  match opd as _opd return [! _opd !] -> Trace with
  | None => fun p => match p with end
  | Some spt => fun p => trace_payload_desc spt f p
  end.

End WITH_TRACE_FUN.

Definition trace_payload_recv := trace_payload_desc trace_recv.

Definition trace_payload_send := trace_payload_desc trace_send.

Definition trace_opt_payload_recv := trace_opt_payload_desc trace_recv.

Definition trace_opt_payload_send := trace_opt_payload_desc trace_send.

Definition num_of_fin (bound : nat) (n : fin bound) := num_of_nat (nat_of_fin n).

Implicit Arguments num_of_fin [bound].

Definition recv_msg (f : fd) (m : msg) : Trace :=
  let t := tag m in
  trace_payload_recv (lkup_tag t) f (pay m) ++ RecvNum f (num_of_fin t).

Definition recv_bogus_msg (f : fd) (m : bogus_msg) : Trace :=
  RecvNum f (btag m).

Definition SendMsg (f : fd) (m : msg) : Trace :=
  let t := tag m in
  trace_payload_send (lkup_tag t) f (pay m) ++ SendNum f (num_of_fin t).

Definition recv_maybe_msg (f : fd) (m : maybe_msg) : Trace :=
  match m with
  | inl m => recv_msg f m
  | inr bm => recv_bogus_msg f bm
  end.

Definition recv_arg :
  forall (f : fd) (ps : list Perm) (t : desc) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
        (fun v : [[ t ]] => tr ~~ traced (trace_recv f t v ++ tr) * open f ps).
Proof.
  intros; refine (
    match t as _t return STsep _ (fun v : [[ _t ]] => _) with
    | num_d =>
      n <- recv_num f ps tr;
      {{ Return n }}
    | str_d =>
      s <- recv_str f ps tr;
      {{ Return s }}
    | fd_d =>
      g <- recv_fd f ps tr;
      {{ Return g }}
    end
  );
  sep'.
Qed.

Definition send_arg :
  forall (f : fd) (ps : list Perm) (d : desc) (v : [[ d ]]) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
        (fun _ : unit => tr ~~ traced (trace_send f d v ++ tr) * open f ps).
Proof.
  intros; refine (
    match d as _d return
      forall v : [[ _d ]],
      STsep _ (fun _ => tr ~~ traced (trace_send f _d v ++ tr) * _)
    with
    | num_d => fun v =>
      send_num f ps v tr;;
      {{ Return tt }}
    | str_d => fun v =>
      send_str f ps v tr;;
      {{ Return tt }}
    | fd_d => fun v =>
      send_fd f ps v tr;;
      {{ Return tt }}
    end v
  );
  sep'.
Qed.

Definition recv_payload' :
  forall (f : fd) (ps : list Perm) (n : nat) (pd : payload_desc' n) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
        (fun pv : [[ pd ]] =>
           tr ~~ traced (trace_payload_desc' trace_recv n pd f pv ++ tr) * open f ps).
Proof.
  intros; refine (
    Fix3
      (fun n pd tr => tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
      (fun n pd tr (pv : [[ pd ]]) =>
         tr ~~ traced (trace_payload_desc' trace_recv n pd f pv ++ tr) * open f ps)
      (fun self (n : nat) (pd : payload_desc' n) tr =>
         match n as _n return
           forall (pd : payload_desc' _n), STsep _ (fun x : [[ pd ]] => _)
         with
         | O => fun _ => {{ Return tt }}
         | S n' => fun pt =>
           match pt with
           | (d, pt') =>
             v  <- recv_arg f ps d tr <@> [In RecvP ps] * [In RecvFDP ps];
             vs <- self n' pt' (tr ~~~ trace_recv f d v ++ tr);
             {{ Return (v, vs) }}
           end
         end pd
      )
    n pd tr
  );
  sep'.
  inv H; rewrite app_assoc; sep'.
Qed.

Definition recv_payload :
  forall (f : fd) (ps : list Perm) (pd : payload_desc) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
        (fun pv : [[ pd ]] =>
           tr ~~ traced (trace_payload_recv pd f pv ++ tr) * open f ps).
Proof.
  intros f ps pd. destruct pd as [n pd].
  exact (recv_payload' f ps n pd).
Qed.

Definition send_payload' :
  forall (f : fd) (ps : list Perm) (n : nat) (pd : payload_desc' n) (pv : [[ pd ]])
         (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
        (fun _ : unit =>
           tr ~~ traced (trace_payload_desc' trace_send n pd f pv ++ tr) * open f ps).
Proof.
  intros; refine (
    Fix4
      (fun n pd pv tr => tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
      (fun n pd pv (tr : [Trace]) _ =>
         tr ~~ traced (trace_payload_desc' trace_send n pd f pv ++ tr) * open f ps)
      (fun self (n : nat) (pd : payload_desc' n) pv (tr : [Trace])
       =>
         match n as _n return
           forall (pd : payload_desc' _n) (pv : [[ pd ]]),
             STsep _ (fun _ => tr ~~ traced (trace_payload_desc' trace_send _n pd f pv ++ tr) * _)
         with
         | O => fun _ _ => {{ Return tt }}
         | S n' => fun (pd : payload_desc' (S n'))
                       (pv : @denote _ (@Denoted_payload_desc' (S n')) pd) =>
           match pd as _pd return
             forall (pv : @denote _ (@Denoted_payload_desc' (S n')) _pd), STsep _ (fun _ => _)
           with
           | (d, pt') => fun pv =>
             match pv with
             | (v, pv') =>
               send_arg f ps d v tr <@> [In SendP ps] * [In SendFDP ps];;
               self n' pt' pv' (tr ~~~ trace_send f d v ++ tr);;
               {{ Return tt }}
             end
           end pv
         end pd pv
      ) n pd pv tr);
  sep';
  try rewrite app_assoc; sep'.
Qed.

Definition send_payload :
  forall (f : fd) (ps : list Perm) (pd : payload_desc) (pv : [[ pd ]]) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
        (fun _ : unit => tr ~~ traced (trace_payload_send pd f pv ++ tr) * open f ps).
Proof.
  intros f ps pd. destruct pd as [n pd].
  exact (send_payload' f ps n pd).
Qed.

Definition recv_msg :
  forall (f : fd) (ps : list Perm) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps] * [In RecvFDP ps])
        (fun m : maybe_msg => tr ~~ traced (recv_maybe_msg f m ++ tr) * open f ps).
Proof.
  intros; refine (
    t <- recv_num f ps tr <@> [In RecvP ps] * [In RecvFDP ps];
    let opt := lkup_tag t in
    match opt as _opt return opt = _opt -> _ with
    | Some pt => fun pf : opt = Some pt =>
      pv <- recv_payload f ps pt (tr ~~~ RecvNum f t ++ tr);
      let pv' := eq_rect_r (x := Some pt) optdenote pv pf in
      {{ Return (inl _ (Build_msg t pv')) }}
    | None => fun pf : opt = None =>
      {{ Return (inr _ (Build_bogus_msg t pf)) }}
    end (refl_equal _)
  );
  sep'; try discriminate;
  match goal with
  | [H: ?inx _ _ = ?inx _ _ |- _] => inv H
  end.
  unfold RecvMsg, pv', eq_rect_r; simpl; rewrite pf; simpl. rewrite app_assoc; sep'.
  unfold recv_bogus_msg. sep'.
Qed.

Definition send_msg :
  forall (f : fd) (ps : list Perm) (m : msg) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps] * [In SendFDP ps])
        (fun _ : unit => tr ~~ traced (SendMsg f m ++ tr) * open f ps).
Proof.
  intros; refine (
    let t := tag m in
    let opt := lkup_tag t in
    match opt as _opt return opt = _opt -> _ with
    | Some pt => fun pf : opt = Some pt =>
      let pv : [[ pt ]] := eq_rect _ _ (pay m) _ pf in
      send_num f ps t tr <@> [In SendP ps] * [In SendFDP ps];;
      send_payload f ps pt pv (tr ~~~ SendNum f t ++ tr);;
      {{ Return tt }}
    | None => fun pf : opt = None =>
      let x : False := eq_rect _ _ (pay m) _ pf in
      False_rec _ x
    end (refl_equal opt)
  );
  sep'.
  unfold SendMsg, t, pv in *. clear t pv. destruct m as [n p]. simpl in *.
  revert p. rewrite pf. simpl. intro. rewrite app_assoc; sep'.
Qed.

Inductive KAction : Type :=
| KExec   : str -> list str -> fd -> KAction
| KCall   : str -> list str -> fd -> KAction
| KSelect : list fd -> fd -> KAction
| KSend   : fd -> msg -> KAction
| KRecv   : fd -> msg -> KAction
| KBogus  : fd -> bogus_msg -> KAction
.

Definition KTrace : Type :=
  list KAction.

Definition expand_kaction (ka : KAction) : Trace :=
  match ka with
  | KExec cmd args f => Exec cmd args f :: nil
  | KCall cmd args pipe => Call cmd args pipe :: nil
  | KSelect cs f => Select cs f :: nil
  | KSend f m => SendMsg f m
  | KRecv f m => RecvMsg f m
  | KBogus f bm => recv_bogus_msg f bm
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

Inductive unop : desc -> desc -> Set :=
| Not : unop num_d num_d
.

Definition eval_unop
  (d1 d2 : desc) (op : unop d1 d2) (v : [[ d1 ]]) : [[ d2 ]] :=
  match op in unop t1 t2 return [[ t1 ]] -> [[ t2 ]] with
  | Not => fun v => if num_eq v FALSE then TRUE else FALSE
  end v.

Implicit Arguments eval_unop.

Inductive binop : desc -> desc -> desc -> Set :=
| Eq  : forall t, binop t t num_d
| Add : binop num_d num_d num_d
| Sub : binop num_d num_d num_d
| Mul : binop num_d num_d num_d
| Cat : binop str_d str_d str_d
.

Definition eval_binop
  (d1 d2 d3: desc) (op : binop d1 d2 d3) (v1 : [[ d1 ]]) (v2 : [[ d2 ]]) : [[ d3 ]] :=
  match op in binop _d1 _d2 _d3 return [[ _d1 ]] -> [[ _d2 ]] -> [[ _d3 ]] with
  | Eq d => fun v1 v2 : [[ d ]] =>
    let teq : forall (x y : [[ d ]]), {x = y} + {x <> y} :=
      match d with
      | num_d => num_eq
      | str_d => str_eq
      | fd_d  => fd_eq
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

(*
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
*)

Section WITH_ENV.

Variable CST : kstate.
Variable CFD : fd.
Variable CMSG : msg.

Print msg.

Let CPAY : option payload_desc := lkup_tag (tag CMSG).

(*
Definition mparam_i (i : nat) : TypeD (optpayload_get_t CPAY i) :=
  match CPAY as opt return
    OptPayloadD opt -> TypeD (optpayload_get_t opt i)
  with
  | Some pt => fun p : PayloadD pt => payload_get_v i pt p
  | None => fun pf : False => False_rec _ pf
  end (pay CMSG).
*)

Inductive base_expr : desc -> Set :=
(* no fd lit, otherwise would make lit ctor polymorphic *)
| NLit : num -> base_expr num_d
| SLit : str -> base_expr str_d
| CurChan : base_expr fd_d
| Param : forall i,
  base_expr (
    match CPAY with
    | None => 
    | Some pd => 
    end
  )
| UnOp :
  forall d1 d2,
  unop d1 d2 ->
  base_expr d1 ->
  base_expr d2
| BinOp :
  forall d1 d2 d3,
  binop d1 d2 d3 ->
  base_expr d1 ->
  base_expr d2 ->
  base_expr d3
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