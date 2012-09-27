Require Import List.
Require Import Ascii.
Require Import Ynot.
Require Import KrakenBase.
Require Import Exchange.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  Ltac unfoldr := unfold kstate_inv.

  Ltac simplr := try (
  match goal with
    | [ |- KTrace _ ] => constructor
  end
  ).

  intros [comps tr];
  refine (
    comp <- select comps tr
    <@> (tr ~~ [KTrace tr] * all_bound comps);
    s' <- exchange comp (mkst comps (tr ~~~ Select comps comp :: tr));
    {{ Return s' }}
  );
  sep unfoldr simplr.
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
