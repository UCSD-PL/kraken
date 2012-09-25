Require Import List.
Require Import Ascii.
Require Import Ynot.
Require Import KrakenBase.
Require Import Exchange.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Record kstate : Set :=
  mkst { components : list chan
       ; ktr : [Trace]
       }.

Inductive KTrace : Trace -> Prop :=
| KT_init :
  forall c,
  KTrace (Exec ("t" :: "e" :: "s" :: "t" :: "." :: "p" :: "y" :: nil) c :: nil)
| KT_select :
  forall tr cs c,
  KTrace tr ->
  KTrace (Select cs c :: tr)
| KT_exchange :
  forall tr1 tr2,
  KTrace tr1 ->
  AddedValidExchange tr1 tr2 ->
  KTrace tr2.

Fixpoint all_bound (cs : list chan) : hprop :=
  match cs with
    | nil => emp
    | c :: cs' => bound c * all_bound cs'
  end.

(* all cs bound except _first_ occurrence of drop *)
Fixpoint all_bound_drop (cs : list chan) (drop : chan) : hprop :=
  match cs with
    | nil => emp
    | c :: cs' =>
      if chan_eq c drop then
        all_bound cs'
      else
        bound c * all_bound_drop cs' drop
  end.

Lemma unpack_all_bound :
  forall cs c,
  In c cs ->
  all_bound cs ==> bound c * all_bound_drop cs c.
Proof.
  induction cs; simpl; intros. contradiction.
  destruct H; subst. rewrite chan_eq_true. apply himp_refl.
  case (chan_eq a c); intros; subst. apply himp_refl.
  apply himp_comm_conc. apply himp_assoc_conc1.
  apply himp_split. apply himp_refl.
  apply himp_comm_conc; auto.
Qed.

Lemma repack_all_bound :
  forall cs c,
  In c cs ->
  bound c * all_bound_drop cs c ==> all_bound cs.
Proof.
  induction cs; simpl; intros. contradiction.
  destruct H; subst. rewrite chan_eq_true. apply himp_refl.
  case (chan_eq a c); intros; subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Definition kstate_inv s : hprop :=
  tr :~~ ktr s in
  traced tr * [KTrace tr] * all_bound (components s).

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  unfold kstate_inv; intros [comps tr];
  refine (
    comp <- select comps
      tr <@>
      (tr ~~ [KTrace tr] * all_bound comps);
    tr' <- exchange comp
      (tr ~~~ Select comps comp :: tr) <@>
      (tr ~~ [KTrace tr] * all_bound_drop comps comp * [In comp comps]);
    {{ Return (mkst comps tr') }}
  );
  sep fail auto.
  apply unpack_all_bound; auto.
  apply himp_comm_conc; apply himp_prop_conc.
  apply KT_exchange in H; auto. constructor; auto.
  apply repack_all_bound; auto.
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
  sep fail auto.
Qed.

Definition kinit :
  forall (_ : unit),
  STsep (traced nil)
        (fun s => kstate_inv s).
Proof.
  intros; refine (

    c <- exec ("t" :: "e" :: "s" :: "t" :: "." :: "p" :: "y" :: nil)
    (inhabits nil);

    {{ Return (mkst (c :: nil) (inhabits (Exec ("t" :: "e" :: "s" :: "t" :: "." :: "p" :: "y" :: nil) c :: nil))) }}

  );
  sep fail auto.
  unfold kstate_inv.
  sep fail auto.
  apply himp_pure'.
  constructor; auto.
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
  unfold kstate_inv;
  sep fail auto.
Qed.
