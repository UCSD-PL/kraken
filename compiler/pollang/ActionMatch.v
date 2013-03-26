Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexVec.
Require Import ReflexHVec.

Section KOAction.

Context {NB_MSG : nat}.
Variable PAYD : vvdesc NB_MSG.

Definition soptdenote_desc (d : desc) : Set :=
  option (sdenote_desc d).

Record opt_msg : Set :=
  { opt_tag : fin NB_MSG
  ; opt_pay : shvec soptdenote_desc (projT2 (lkup_tag PAYD opt_tag))
  }.

Inductive KOAction : Set :=
| KOExec   : option str -> option (list (option str)) -> option fd -> KOAction
| KOCall   : option str -> option (list (option str)) -> option fd -> KOAction
| KOSelect : option (list (option fd)) -> option fd -> KOAction
| KOSend   : option fd -> option opt_msg -> KOAction
| KORecv   : option fd -> option opt_msg -> KOAction
| KOBogus  : option fd -> option num -> KOAction.

Definition eltMatch (d:desc) (opt:option s[[d]]) (arg:s[[d]]) : Prop :=
  match opt with
  | None   => True
  | Some t => t = arg
  end.

Definition msgMatch' (optm:opt_msg) (m:msg PAYD) : Prop :=
  let opt_tag := (opt_tag optm) in
  let tag := (tag _ m) in
  match fin_eq_dec tag opt_tag with
  | left H => match H in eq _ _tag return
                shvec soptdenote_desc (projT2 (lkup_tag PAYD _tag)) -> Prop
              with
              | eq_refl => fun opt_pay =>
                 shvec_match_prop (projT2 (lkup_tag PAYD tag))
                                  soptdenote_desc sdenote_desc
                                  eltMatch opt_pay (pay _ m)
              end (opt_pay optm)
  | right H => False
  end.

Definition msgMatch (opt_optm:option opt_msg) (m:msg _) : Prop :=
  match opt_optm with
  | None => True
  | Some optm => msgMatch' optm m
  end.

Fixpoint listMatch' (d:desc)
           (lopt:list (option s[[d]])) (l:list s[[d]]) : Prop :=
  match lopt, l with
  | nil, nil          => True
  | opt::lopt', e::l' => eltMatch d opt e /\ listMatch' d lopt' l'
  | _, _              => False
  end.

Definition listMatch (d:desc)
  (lopt:option (list (option s[[d]]))) (l:list s[[d]]) :=
  match lopt with
  | None => True
  | Some lopt' => listMatch' d lopt' l
  end.

Definition AMatch (oact:KOAction) (act:KAction PAYD) : Prop :=
match oact, act with
| KOExec s ls f, KExec s' ls' f' => eltMatch str_d s s' /\
                                    listMatch str_d ls ls'  /\
                                    eltMatch fd_d f f'
| KOCall s ls f, KCall s' ls' f' => eltMatch str_d s s' /\
                                    listMatch str_d ls ls' /\
                                    eltMatch fd_d f f'
| KOSelect lfd f, KSelect lfd' f' => listMatch fd_d lfd lfd' /\
                                     eltMatch fd_d f f'
| KOSend f omsg, KSend f' amsg => eltMatch fd_d f f' /\
                                  msgMatch omsg amsg
| KORecv f omsg, KRecv f' amsg => eltMatch fd_d f f' /\
                                  msgMatch omsg amsg
(**I don't know if this is the right thing to do for KBogus matching.
   It just checks if the message tags and fds are the same**)
| KOBogus f optbtag, KBogus f' bmsg => eltMatch fd_d f f' /\
                                       eltMatch num_d optbtag (btag bmsg)
| _, _ => False
end.

End KOAction.

Lemma decide_and : forall P Q, decide P ->
                               decide Q ->
                               decide (P /\ Q).
Proof.
  tauto.
Qed.

Definition decide_elt_match : forall d oelt elt,
                                decide (eltMatch d oelt elt).
Proof.
  destruct oelt;
  [ destruct d; [apply num_eq | apply str_eq | apply fd_eq]
  | auto].
Qed.

Definition decide_list_match : forall d lopt l,
                                 decide (listMatch d lopt l).
Proof.
  intros d lopt l.
  destruct lopt as [lopt' | ]; simpl; auto.
    generalize dependent l; induction lopt'; destruct l; simpl; auto.
      apply decide_and; [apply decide_elt_match | apply IHlopt'].
Qed.

Definition decide_msg_match : forall {NB_MSG} (PAYD:vvdesc NB_MSG) opt_optm m,
                                decide (msgMatch PAYD opt_optm m).
Proof.
  intros NB_MSG PAYD opt_optm m.
  destruct opt_optm as [optm | ];
  [destruct optm as [otag opay]; simpl
  | auto ].
    unfold msgMatch'; simpl;
    match goal with
    |- context[fin_eq_dec ?x ?y ]
      => destruct (fin_eq_dec x y) as [eq | ]; [destruct eq | auto]
    end.
    destruct m as [tag pay]; simpl in *.
    destruct (lkup_tag PAYD tag) as [n vd].
    induction n; auto.
      simpl in *.
      destruct vd as [d vd'].
      destruct opay as [oelt orest].
      destruct pay as [elt rest].
      apply decide_and; [apply decide_elt_match | auto].
Qed.

Definition decide_act : forall {NB_MSG} (PAYD:vvdesc NB_MSG) oact act,
                          decide (AMatch PAYD oact act).
Proof.
  intros NB_MSG PAYD oact act.
  destruct oact; destruct act; simpl; auto; (*Takes care of decide (False)*)
  repeat apply decide_and;
  match goal with
  | [ |- decide (eltMatch _ _ _) ] => apply decide_elt_match
  | [ |- decide (listMatch _ _ _) ] => apply decide_list_match
  | [ |- decide (msgMatch _ _ _) ] => apply decide_msg_match
  end.
Qed.
