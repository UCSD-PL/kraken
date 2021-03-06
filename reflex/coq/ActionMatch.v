Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexIO.
Require Import ReflexVec.
Require Import ReflexHVec.

Section KOAction.

Context {NB_MSG : nat}.
Variable PAYD : vvdesc NB_MSG.
Variable COMPT : Set.
Variable COMPS : COMPT -> compd.
Variable COMPTDEC : forall (x y : COMPT), decide (x = y).
Definition conc_pat := conc_pat COMPT COMPS.

Definition soptdenote_desc (d : desc) : Set :=
  option (sdenote_desc d).

Record opt_msg : Set :=
  { opt_tag : fin NB_MSG
  ; opt_pay : shvec soptdenote_desc (projT2 (lkup_tag PAYD opt_tag))
  }.

Inductive KOAction : Set :=
| KOExec      : option str -> option (list (option str)) -> option conc_pat
                -> KOAction
| KOCall      : option str -> option (list (option str)) -> option fd -> KOAction
| KOInvokeFD  : option str -> option (list (option str)) -> option fd -> KOAction
| KOInvokeStr : option str -> option (list (option str)) -> option str -> KOAction
| KOSelect    : option (list (option conc_pat)) -> option conc_pat -> KOAction
| KOSend      : option conc_pat -> option opt_msg -> KOAction
| KORecv      : option conc_pat -> option opt_msg -> KOAction
| KOBogus     : option conc_pat -> option num -> KOAction.

Definition eltMatch (d:desc) (opt:option s[[d]]) (arg:s[[d]]) : Prop :=
  match opt with
  | None   => True
  | Some t => t = arg
  end.

Definition match_comp' (cp : conc_pat) (c : comp COMPT COMPS) : Prop :=
  match c, cp with
  | Build_comp t f cfg, Build_conc_pat t' cfgp =>
    match COMPTDEC t t' with
    | left EQ =>
      match EQ in _ = _t return
        shvec sdenote_desc_conc_pat (projT2 (comp_conf_desc _ _ _t)) -> Prop
      with
      | Logic.eq_refl => fun cfgp =>
        shvec_match_prop (projT2 (comp_conf_desc _ _ t))
                         soptdenote_desc sdenote_desc
                         eltMatch cfgp cfg
      end cfgp
    | right _ => False
    end
  end.

Definition match_comp (cpopt:option conc_pat) (c:comp COMPT COMPS) : Prop :=
  match cpopt with
  | None    => True
  | Some cp => match_comp' cp c
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

Fixpoint comp_list_match'
  (lopt:list (option conc_pat)) (l:list (comp COMPT COMPS)) :=
  match lopt, l with
  | nil, nil          => True
  | cpopt::lopt', c::l' => match_comp cpopt c /\ comp_list_match' lopt' l'
  | _, _              => False
  end.

Definition comp_list_match
  (lopt:option (list (option conc_pat))) (l:list (comp COMPT COMPS)) :=
  match lopt with
  | None => True
  | Some lopt' => comp_list_match' lopt' l
  end.

Definition AMatch (oact:KOAction) (act:KAction PAYD COMPT COMPS) : Prop :=
match oact, act with
| KOExec s ls c, KExec s' ls' c' => eltMatch str_d s s' /\
                                    listMatch str_d ls ls'  /\
                                    match_comp c c'
| KOCall s ls f, KCall s' ls' f' => eltMatch str_d s s' /\
                                    listMatch str_d ls ls' /\
                                    eltMatch fd_d f f'
| KOInvokeFD s ls f, KInvokeFD s' ls' f' => eltMatch str_d s s' /\
                                            listMatch str_d ls ls' /\
                                            eltMatch fd_d f f'
| KOInvokeStr s ls res, KInvokeStr s' ls' res' => eltMatch str_d s s' /\
                                                  listMatch str_d ls ls' /\
                                                  eltMatch str_d res res'
| KOSelect lcps cp, KSelect lcs c => comp_list_match lcps lcs /\
                                     match_comp cp c
| KOSend cp omsg, KSend c amsg => match_comp cp c /\
                                  msgMatch omsg amsg
| KORecv cp omsg, KRecv c amsg => match_comp cp c /\
                                  msgMatch omsg amsg
(**I don't know if this is the right thing to do for KBogus matching.
   It just checks if the message tags and fds are the same**)
| KOBogus cp optbtag, KBogus c bmsg => match_comp cp c /\
                                       eltMatch num_d optbtag (btag bmsg)
| _, _ => False
end.

End KOAction.

(* Hints are lost on Section closure, so keep them out to be exported *)
Hint Unfold eltMatch.
Hint Unfold listMatch.
Hint Unfold match_comp.
Hint Unfold match_comp'.
Hint Unfold msgMatch.
Hint Unfold msgMatch'.
Hint Unfold AMatch.

Lemma decide_and : forall P Q,
  decide P ->
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

Definition decide_shvec_match :
  forall n (vd:svec desc n) v v',
    decide (shvec_match_prop vd soptdenote_desc sdenote_desc eltMatch v v').
Proof.
  intros n vd v v'.
  induction n; auto.
      simpl in *.
      destruct vd as [d vd'].
      destruct v as [oelt orest].
      destruct v' as [elt rest].
      apply decide_and; [apply decide_elt_match | auto].
Qed.

Definition decide_match_comp' :
  forall COMPT COMPS COMPTDEC cp c,
    decide (match_comp' COMPT COMPS COMPTDEC cp c).
Proof.
  intros COMPT COMPS COMPTDEC cp c.
  destruct cp; destruct c.
  unfold match_comp'.
  match goal with
  |- context[COMPTDEC ?comp_type ?comp_pat_type]
    => destruct (COMPTDEC comp_type comp_pat_type) as [eq | ];
       [destruct eq | auto]
  end.
  apply decide_shvec_match.
Qed.

Definition decide_match_comp :
  forall COMPT COMPS COMPTDEC cpopt c,
    decide (match_comp COMPT COMPS COMPTDEC cpopt c).
Proof.
  intros COMPT COMPS COMPTDEC cpopt c.
  destruct cpopt as [cp | ]; [simpl; destruct cp; destruct c | auto].
  apply decide_match_comp'.
Qed.

Definition decide_list_match_comp :
  forall COMPT COMPS COMPTDEC lopt l,
    decide (comp_list_match COMPT COMPS COMPTDEC lopt l).
Proof.
  intros COMPT COMPS COMPTDEC lopt l.
  destruct lopt as [lopt' | ]; simpl; auto.
    generalize dependent l; induction lopt'; destruct l; simpl; auto.
      apply decide_and; [apply decide_match_comp | apply IHlopt'].
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
    apply decide_shvec_match.
Qed.

Definition decide_act :
  forall {NB_MSG} (PAYD:vvdesc NB_MSG) COMPT COMPS COMPTDEC oact act,
    decide (AMatch PAYD COMPT COMPS COMPTDEC oact act).
Proof.
  intros NB_MSG PAYD COMPT COMPS COMPTDEC oact act.
  destruct oact; destruct act; simpl; auto; (*Takes care of decide (False)*)
  repeat apply decide_and;
  match goal with
  | [ |- decide (eltMatch _ _ _) ] => apply decide_elt_match
  | [ |- decide (listMatch _ _ _) ] => apply decide_list_match
  | [ |- decide (msgMatch _ _ _) ] => apply decide_msg_match
  | [ |- decide (match_comp _ _ _ _ _) ] => apply decide_match_comp
  | [ |- decide (comp_list_match _ _ _ _ _) ] => apply decide_list_match_comp
  end.
Qed.
