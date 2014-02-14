Require Import ReflexBase.
Require Import Reflex.
Require Import String.
Require Import List.
Require Import ReflexIO.
Require Import ReflexFin.
Require Import ReflexVec.
Require Import ReflexDenoted.

Definition id := string.
Definition tag := string.
Definition var_list COMPT := list (id * cdesc COMPT).

Fixpoint mk_vdesc' l : vdesc' (List.length l) :=
  match l with
  | nil     => tt
  | x :: xs => (x, mk_vdesc' xs)
  end.

Definition mk_vdesc l : vdesc := existT _ (List.length l) (mk_vdesc' l).

Fixpoint mk_vcdesc' {COMPT} l : vcdesc' COMPT (List.length l) :=
  match l with
  | nil     => tt
  | x :: xs => (x, mk_vcdesc' xs)
  end.

Definition mk_vcdesc {COMPT} l : vcdesc COMPT := existT _ (List.length l) (mk_vcdesc' l).

Definition cdesc_eqdec {COMPT:Set} (COMPTDEC:forall (c1 c2:COMPT), decide (c1=c2))
  (c1 c2:cdesc COMPT) : decide (c1 = c2).
destruct c1; destruct c2.
  destruct (desc_eqdec d d0).
    subst d; auto.

    right. unfold not. intro H.
    inversion H. auto.

  right. unfold not. intro H. inversion H.

  right. unfold not. intro H. inversion H.

  destruct (COMPTDEC c c0).
    subst c; auto.

    right. unfold not. intro H.
    inversion H. auto.
Defined.

Definition vcdesc_eqdec {COMPT:Set} (COMPTDEC:forall (c1 c2:COMPT), decide (c1=c2))
  (v1 v2:vcdesc COMPT) : decide (v1=v2).
destruct v1. destruct v2.
destruct (Peano_dec.eq_nat_dec x x0). subst x.
induction x0.
  simpl in *. destruct v. destruct v0. auto.

  simpl in *. destruct v. destruct v0.
  destruct (cdesc_eqdec COMPTDEC c c0).
    destruct (IHx0 v v0).
      subst c. left. apply Eqdep_dec.inj_pair2_eq_dec in e0.
      congruence. apply Peano_dec.eq_nat_dec.

      right. unfold not. intro H.
      apply Eqdep_dec.inj_pair2_eq_dec in H.
      congruence. apply Peano_dec.eq_nat_dec.

    right. unfold not. intro H.
    apply Eqdep_dec.inj_pair2_eq_dec in H.
    congruence. apply Peano_dec.eq_nat_dec.

right. unfold not. intro H. congruence.
Defined.

Definition vdesc_eqdec (v1:vdesc) (v2:vdesc) : decide (v1=v2).
destruct v1. destruct v2.
destruct (Peano_dec.eq_nat_dec x x0). subst x.
induction x0.
  simpl in *. destruct v. destruct v0. auto.

  simpl in *. destruct v. destruct v0.
  destruct (desc_eqdec d d0).
    destruct (IHx0 v v0).
      subst d. left. apply Eqdep_dec.inj_pair2_eq_dec in e0.
      congruence. apply Peano_dec.eq_nat_dec.

      right. unfold not. intro H.
      apply Eqdep_dec.inj_pair2_eq_dec in H.
      congruence. apply Peano_dec.eq_nat_dec.

    right. unfold not. intro H.
    apply Eqdep_dec.inj_pair2_eq_dec in H.
    congruence. apply Peano_dec.eq_nat_dec.

right. unfold not. intro H. congruence.
Defined.

Inductive maybe (A:Set) : Set :=
| Yes : A -> maybe A
| No  : maybe A.

Implicit Arguments Yes [A].
Implicit Arguments No [A].

Definition mmap {A B:Set} (f:A->B) (m:maybe A) : maybe B :=
  match m with
  | Yes x => Yes (f x)
  | No    => No
  end.

Inductive expr : Type :=
| ConstN : num    -> expr
| ConstS : str    -> expr
| Var    : id -> expr
| Unop   : forall {d1 d2:desc},
  (s[[d1]] -> s[[d2]]) -> expr -> expr
| Binop  : forall {d1 d2 d3:desc},
  (s[[d1]] -> s[[d2]] -> s[[d3]]) -> expr -> expr -> expr.

Inductive cmd : Type :=
| Nop    : cmd
| Assign : id -> expr -> cmd
| Send   : expr (*comp*) -> tag (*msgt*) -> list expr -> cmd
| Spawn  : id (*local*) -> tag (*compt*) -> list expr -> cmd
| Call   : id (*local*) -> expr (*command*) -> list expr (*args*) -> cmd
| Ite    : expr (*cond*) -> cmd (*then*) -> cmd (*else*) -> cmd
| Seq    : cmd -> cmd -> cmd
| Lookup : id -> tag (*compt*) -> list (option expr) (*cfg*) -> cmd -> cmd -> cmd.

Record handler := mk_hdlr
  { hdlr_compt : tag;
    hdlr_msgt  : tag;
    hdlr_cmd   : cmd
  }.

Record msg := mk_msg
  { msgt     : tag;
    msg_payt : list desc
  }.

Record comp := mk_comp
  { compt     : tag;
    path      : string;
    args      : list string;
    comp_cfgt : list desc
  }.

Definition mk_compt (cs:list comp) : Set := fin (List.length cs).

Record prog := mk_prog
  { comps : list comp;
    msgs  : list msg;
    state : var_list (mk_compt comps);
    init  : cmd;
    hdlrs : list handler
  }.

Fixpoint mk_payd (ms:list msg) : vvdesc (List.length ms) :=
  match ms with
  | nil     => tt
  | m :: ms => (mk_vdesc (msg_payt m), mk_payd ms)
  end.

Fixpoint mk_compt_map (cs:list comp) : tag -> maybe (mk_compt cs) :=
  match cs as _cs return
    tag -> maybe (mk_compt _cs)
  with
  | nil      => fun _ => No
  | c :: cs' => fun t =>
    if string_dec (compt c) t
    then Yes None
    else mmap lift_fin (mk_compt_map cs' t)
  end.

Fixpoint mk_comps (cs:list comp) : mk_compt cs -> compd :=
  match cs as _cs return
    mk_compt _cs -> compd
  with
  | nil     => fun i => match i with end
  | c :: cs' =>
    fun i =>
      match i with
      | None => {| compd_name:=str_of_string (compt c);
                   compd_cmd:=str_of_string (path c);
                   compd_args:=map str_of_string (args c);
                   compd_conf:=mk_vdesc (comp_cfgt c)
                 |}
      | Some i' => mk_comps cs' i'
      end
  end.

Definition mk_var_d {COMPT} (l:var_list COMPT) :=
  mk_vcdesc (map (@snd id (cdesc COMPT)) l).

Fixpoint get_fin (l:list string) :
  string -> maybe (fin (List.length l)) :=
  match l as _l return
    string -> maybe (fin (List.length _l))
  with
  | nil          => fun _ => No
  | v :: l' => fun v' =>
    if string_dec v v'
    then Yes None
    else mmap lift_fin (get_fin l' v')
  end.

Definition map_length : forall (A B : Type) (f : A -> B) (l : list A),
  Datatypes.length (map f l) = Datatypes.length l.
induction l.
  reflexivity.

  simpl. rewrite IHl. reflexivity.
Defined.

Definition get_var_fin {COMPT} (l:var_list COMPT) :
  id -> maybe (fin (List.length (map (@snd id (cdesc COMPT)) l))).
  rewrite map_length. rewrite <- map_length with (f:=@fst id (cdesc COMPT)).
  exact (get_fin (map (@fst id (cdesc COMPT)) l)).
Defined.

Fixpoint has_var {COMPT} (l:var_list COMPT) (s:string) : bool :=
  match l with
  | nil          => false
  | (v, _) :: l' =>
    if string_dec s v
    then true
    else has_var l' s
  end.

Definition get_msg_fin (l:list msg) :
  tag -> maybe (fin (List.length l)).
  rewrite <- map_length with (f:=msgt).
  exact (get_fin (map msgt l)).
Defined.

Definition get_comp_fin (l:list comp) :
  tag -> maybe (fin (List.length l)).
  rewrite <- map_length with (f:=compt).
  exact (get_fin (map compt l)).
Defined.

(*Fixpoint get_var_fin {COMPT} (l:var_list COMPT) :
  id -> maybe (fin (List.length (map (@snd id (cdesc COMPT)) l))) :=
  match l as _l return
    id -> maybe (fin (List.length (map (@snd id (cdesc COMPT)) _l)))
  with
  | nil          => fun _ => No
  | (v, _) :: l' => fun v' =>
    if string_dec v v'
    then Yes None
    else mmap lift_fin (get_var_fin l' v')
  end.*)

(*Definition mk_envd COMPT (c:cmd) (ctm:tag->maybe COMPT) : { l : list (tag * cdesc COMPT) | NoDup l }.
  induction c.
    (*Assign*) exact (exist _ nil (NoDup_nil _)).
    (*Send*)  exact (exist _ nil (NoDup_nil _)).
    (*Spawn*) destruct (ctm t).
      exact (Yes (mk_vcdesc ((Comp COMPT c)::nil))).
      exact No.
    (*Ite*)*)

Fixpoint mk_expr_init_cdesc {COMPT} (e:expr) (envd_l:var_list COMPT) :
  option (cdesc COMPT) :=
  let envd := mk_var_d envd_l in
  match e with
  | ConstN n       =>
    Some (Desc COMPT num_d)
  | ConstS s       =>
    Some (Desc COMPT str_d)
  | Var i          =>
    match get_var_fin envd_l i with
    | Yes i' =>
      Some (svec_ith (projT2 envd) i')
    | No     => None
    end
  | Unop d1 d2 op e      =>
    match d2 with
    | fd_d => None
    | _    =>
      match mk_expr_init_cdesc e envd_l with
      | Some c =>
        match c with
        | Desc d1' => if desc_eqdec d1 d1' then Some (Desc _ d2) else None
        | Comp c => None
        end
      | None    => None
      end
    end
  | Binop d1 d2 d3 op e1 e2 =>
    match d3 with
    | fd_d => None
    | _    =>
      match mk_expr_init_cdesc e1 envd_l, mk_expr_init_cdesc e2 envd_l with
      | Some c1, Some c2 =>
        match c1, c2 with
        | Desc d1', Desc d2' =>
          if desc_eqdec d1 d1'
          then if desc_eqdec d2 d2' then Some (Desc _ d3) else None
          else None
        | _, _ => None
        end
      | _, _ => None
      end
    end
  end.

Fixpoint mk_lexpr_init_vdesc {COMPT} (l:list expr) (envd_l:var_list COMPT) :
  option (vdesc' (List.length l)) :=
  match l with
  | nil     => Some tt
  | e :: l' =>
    match mk_expr_init_cdesc e envd_l with
    | Some (Desc d) =>
      match mk_lexpr_init_vdesc l' envd_l with
      | Some v => Some (d, v)
      | None   => None
      end
    | _   => None
    end
  end.

Fixpoint mk_lexpr_init_vcdesc {COMPT} (l:list expr) (envd_l:var_list COMPT) :
  option (vcdesc' COMPT (List.length l)) :=
  match l as _l return
    option (vcdesc' COMPT (List.length _l))
  with
  | nil     => Some tt
  | e :: l' =>
    match mk_expr_init_cdesc e envd_l with
    | Some c =>
      match mk_lexpr_init_vcdesc l' envd_l with
      | Some v => Some (c, v)
      | None   => None
      end
    | _   => None
    end
  end.

Definition mk_expr_init_rt {COMPT} COMPS (e:expr) (envd_l:var_list COMPT) :=
  match mk_expr_init_cdesc e envd_l with
  | Some c => Reflex.expr COMPT COMPS (base_term COMPT) (mk_var_d envd_l) c
  | None => unit
  end.

Definition mk_lexpr_init_rt {COMPT} COMPS (l:list expr) (envd_l:var_list COMPT) :=
  match mk_lexpr_init_vdesc l envd_l with
  | Some c => payload_expr COMPT COMPS (base_term COMPT) (mk_var_d envd_l)
    (existT _ (List.length l) c)
  | None => unit
  end.

Fixpoint mk_expr_init {COMPT} COMPS (e:expr) (envd_l:var_list COMPT) :
  mk_expr_init_rt COMPS e envd_l.
refine(
  let envd := mk_var_d envd_l in
  match e as _e return
    mk_expr_init_rt COMPS _e envd_l
  with
  | ConstN n       =>
    Term COMPT COMPS (base_term COMPT) envd (NLit COMPT envd n)
  | ConstS s       =>
    Term COMPT COMPS (base_term COMPT) envd (SLit COMPT envd s)
  | Var i          => _
(*    match get_var_fin envd_l i with
    | Yes i' =>
      _ (*Term COMPT COMPS (base_term COMPT) envd (Reflex.Var COMPT envd i')*)
    | No     => _
    end*)
  | Unop d1 d2 op e'     => _
(*    match mk_expr_init_cdesc e envd_l with
    | Some (Desc d1') => _
    | _        => tt
    end*)
(*    match d2 as _d2 return
      (s[[d1]] -> s[[_d2]]) -> _
    with
    | num_d => fun op => UnOp COMPT COMPS (base_term COMPT) envd
      (UnopNum COMPT COMPS (Desc _ d1) op) (mk_expr_init COMPT COMPS e envd_l)
    | str_d => _
    end*)
  | Binop _ _ _ op e1 e2 =>
    _ (*BinOp COMPT COMPS (base_term COMPT) envd op (mk_expr_init COMPS e envd)*)
  end).
unfold mk_expr_init_rt. simpl. destruct (get_var_fin envd_l i).
exact (Term COMPT COMPS (base_term COMPT) (mk_var_d envd_l) (Reflex.Var COMPT (mk_var_d envd_l) f)).
exact tt.

specialize (mk_expr_init COMPT COMPS e' envd_l).
unfold mk_expr_init_rt in *.
simpl in *. destruct (mk_expr_init_cdesc e' envd_l).
destruct c. destruct (desc_eqdec d1 d). destruct d2.
subst d1.
exact (UnOp COMPT COMPS (base_term COMPT) envd
  (UnopNum COMPT COMPS (Desc _ d) op) mk_expr_init).
subst d1.
exact (UnOp COMPT COMPS (base_term COMPT) envd
  (UnopStr COMPT COMPS (Desc _ d) op) mk_expr_init).
exact tt.
destruct d2; exact tt.
destruct d2; exact tt.
destruct d2; exact tt.

unfold mk_expr_init_rt in *. simpl in *.
destruct (mk_expr_init_cdesc e1 envd_l) as [? | ?]_eqn.
destruct (mk_expr_init_cdesc e2 envd_l) as [? | ?]_eqn.
destruct c. destruct c0. destruct (desc_eqdec d1 d).
destruct(desc_eqdec d2 d0).
set (e1':=mk_expr_init COMPT COMPS e1 envd_l). rewrite Heqo in e1'.
set (e2':=mk_expr_init COMPT COMPS e2 envd_l). rewrite Heqo0 in e2'.
destruct d3.
subst d1. subst d2.
exact (BinOp COMPT COMPS (base_term COMPT) envd
  (BinopNum COMPT COMPS (Desc _ d) (Desc _ d0) op) e1' e2').
subst d1. subst d2.
exact (BinOp COMPT COMPS (base_term COMPT) envd
  (BinopStr COMPT COMPS (Desc _ d) (Desc _ d0) op) e1' e2').
exact tt.
destruct d3; exact tt.
destruct d3; exact tt.
destruct d3; exact tt.
destruct d3; exact tt.
destruct d3; exact tt.
destruct d3; exact tt.
Defined.

Definition mk_lexpr_init {COMPT} COMPS (l:list expr) (envd_l:var_list COMPT) :
  mk_lexpr_init_rt COMPS l envd_l.
induction l.
  exact tt.

  unfold mk_lexpr_init_rt in *. simpl in *.
  destruct (mk_expr_init_cdesc a envd_l) as [? | ?]_eqn.
  destruct (mk_lexpr_init_vdesc l envd_l). destruct c.
  set (e:=mk_expr_init COMPS a envd_l).
  unfold mk_expr_init_rt in *. rewrite Heqo in e.
  exact (e, IHl).
  exact tt.
  destruct c; exact tt.
  exact tt.
Defined.

Definition mk_init_call_args {COMPT} COMPS (l:list expr) (envd_l:var_list COMPT) :
  option (list (Reflex.expr COMPT COMPS (base_term COMPT) (mk_var_d envd_l) (Desc COMPT str_d))).
induction l.
  exact (Some nil).

  destruct (mk_expr_init_cdesc a envd_l) as [? | ?]_eqn.
    destruct c.
      destruct d.
        exact None.

        destruct IHl.
          set (e:=mk_expr_init COMPS a envd_l).
          unfold mk_expr_init_rt in e. rewrite Heqo in e.
          exact (Some (e :: l0)).

          exact None.

        exact None.

      exact None.

    exact None.
Defined.

Fixpoint get_init_envd_l (cs:list comp) (c:cmd)
  (l:var_list (mk_compt cs)) : var_list (mk_compt cs) :=
  match c with
  | Nop => nil
  | Assign _ _ => l
  | Send _ _ _ => l
  | Spawn i t _ =>
    match get_comp_fin cs t with
    | Yes f => if has_var l i then l else (i, Comp _ f) :: l
    | No   => l
    end
  | Call i _ _ => if has_var l i then l else (i, Desc _ fd_d) :: l
  | Seq c1 c2  =>
    get_init_envd_l cs c2 (get_init_envd_l cs c1 l)
  | Ite _ c1 c2 =>
    get_init_envd_l cs c2 (get_init_envd_l cs c1 l)
  | Lookup i t _ c1 c2 =>
    let l' := match get_comp_fin cs t with
              | Yes f => if has_var l i then l else (i, Comp _ f) :: l
              | No   => l
              end in
    get_init_envd_l cs c2 (get_init_envd_l cs c1 l')
  end.

Definition mk_init (p:prog) (envd_l:var_list (mk_compt (comps p))) :
  let COMPT := mk_compt (comps p) in
  option (init_prog (mk_payd (msgs p)) COMPT
    (mk_comps (comps p)) (mk_var_d (state p))
    (mk_var_d envd_l)).
destruct p.
  simpl in *. clear hdlrs0.
  induction init0.
    (*Nop*)
    exact (Some (Reflex.Nop _ _ _ _ _ _)).

    (*Assign*)
    destruct (mk_expr_init_cdesc e envd_l) as [? | ?]_eqn.
      set (e':=mk_expr_init (mk_comps comps0) e envd_l).
      unfold mk_expr_init_rt in e'. rewrite Heqo in e'.
      destruct (get_var_fin state0 i).
        destruct (cdesc_eqdec fin_eq_dec c (svec_ith (projT2 (mk_var_d state0)) f)).
          subst c.
          exact (Some (StUpd _ _ _ (mk_var_d state0) _ _ f e')).

          exact None.

        exact None.

      exact None.

    (*Send*)
    destruct (get_msg_fin msgs0 t).
      destruct (mk_expr_init_cdesc e envd_l) as [? | ?]_eqn.
        destruct c.
          exact None.

          destruct (mk_lexpr_init_vdesc l envd_l) as [? | ?]_eqn.
            destruct (vdesc_eqdec (existT _ _ v) (vec_ith (mk_payd msgs0) f)).
              set (l':=mk_lexpr_init (mk_comps comps0) l envd_l).
              unfold mk_lexpr_init_rt in l'. rewrite Heqo0 in l'.
              rewrite e0 in l'. set (e':=mk_expr_init (mk_comps comps0) e envd_l).
              unfold mk_expr_init_rt in e'. rewrite Heqo in e'.
              exact (Some (Reflex.Send _ _ _ (mk_var_d state0) _ _ _ e' f l')).

              exact None.

            exact None.

          exact None.

        exact None.

    (*Spawn*)
    destruct (get_var_fin envd_l i).
      destruct (get_comp_fin comps0 t).
        destruct (cdesc_eqdec fin_eq_dec (svec_ith (projT2 (mk_var_d envd_l)) f) (Comp _ f0)).
          destruct (mk_lexpr_init_vdesc l envd_l) as [? | ?]_eqn.
            destruct (vdesc_eqdec (existT _ _ v) (compd_conf (mk_comps comps0 f0))).
              set (l':=mk_lexpr_init (mk_comps comps0) l envd_l).
              unfold mk_lexpr_init_rt in l'. rewrite Heqo in l'.
              rewrite e0 in l'.
              exact (Some (Reflex.Spawn _ _ _ (mk_var_d state0) _ _ _ l' f e)).

              exact None.

            exact None.

          exact None.

        exact None.

      exact None.

    (*Call*)
    destruct (get_var_fin envd_l i).
      destruct (mk_expr_init_cdesc e envd_l) as [? | ?]_eqn.
        destruct c.
          destruct d.
            exact None.

            set (l':=mk_init_call_args (mk_comps comps0) l envd_l).
            destruct l'.
              destruct (cdesc_eqdec fin_eq_dec (svec_ith (projT2 (mk_var_d envd_l)) f) (Desc _ fd_d)).
                set (e':=mk_expr_init (mk_comps comps0) e envd_l).
                unfold mk_expr_init_rt in e'. rewrite Heqo in e'.
                exact (Some (Reflex.Call _ _ _ (mk_var_d state0) _ _ e' l0 f e0)).

                exact None.

              exact None.

            exact None.

          exact None.

        exact None.
 
      exact None.

    (*Ite*)
    destruct (mk_expr_init_cdesc e envd_l) as [? | ?]_eqn.
      destruct c.
        destruct d.
          destruct IHinit0_1.
            destruct IHinit0_2.
              set (e':=mk_expr_init (mk_comps comps0) e envd_l).
              unfold mk_expr_init_rt in e'. rewrite Heqo in e'.          
              exact (Some (Reflex.Ite _ _ _ (mk_var_d state0) _ _ e' i i0)).

              exact None.

            exact None.

          exact None.

        exact None.

      exact None.

    exact None.

    (*Seq*)
    destruct IHinit0_1.
      destruct IHinit0_2.
        exact (Some (Reflex.Seq _ _ _ (mk_var_d state0) _ _ i i0)).

        exact None.

      exact None.

    (*Lookup*)
    destruct (get_var_fin envd_l i).
      destruct (get_comp_fin comps0 t).
        destruct (cdesc_eqdec fin_eq_dec (svec_ith (projT2 (mk_var_d envd_l)) f) (Comp _ f0)).
          destruct (mk_lexpr_init_vdesc l envd_l) as [? | ?]_eqn.
            destruct (vdesc_eqdec (existT _ _ v) (compd_conf (mk_comps comps0 f0))).
              set (l':=mk_lexpr_init (mk_comps comps0) l envd_l).
              unfold mk_lexpr_init_rt in l'. rewrite Heqo in l'.
              rewrite e0 in l'.
              destruct IHinit0_1.
                destruct IHinit0_2.
                  exact (Some (Reflex.CompLkup _ _ _ (mk_var_d state0) _ _
                    (Build_comp_pat (mk_compt comps0) (mk_comps comps0) _ _ f0 l') f e i0 i1)).
Defined.

Open Scope string_scope.
Notation "c1 ; c2" := (Seq c1 c2) (at level 11, right associativity).
Notation "v <- e" := (Assign v e) (at level 10).
Notation "0" := (ConstN (num_of_nat 0)).
Notation "1" := (ConstN (num_of_nat 1)).
Notation "2" := (ConstN (num_of_nat 2)).
Notation "'Components' : cs 'Messages' : ms 'State' : s 'Init' : i 'Handlers' : hs" :=
  (mk_prog cs ms s i hs) (at level 9).

Definition test :=
  Components :
    nil

  Messages :
    nil

  State :
    ("x1", Desc _ num_d) :: nil

  Init :
    "x1" <- 1;
    "x1" <- 0;
    "x1" <- 2

  Handlers :
    nil.

Goal False.
set (t:=mk_init test (get_init_envd_l (comps test) (init test) nil)).
Time simpl in *; unfold mk_var_d, mk_compt, eq_rect_r in *; simpl in *.
    
(*Dont forget about message payload and comp cfg binders.*)
Definition mk_handlers (p:prog) :
  option (handlers (mk_payd (msgs p)) (mk_compt (comps p))
    (mk_comps (comps p)) (mk_state_d (state p))).