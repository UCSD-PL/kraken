Require Import Reflex.
Require Import ReflexBase.
Require Import ActionMatch.
Require Import List.

Section PolLang.

Variable NB_MSG:nat.
Variable PLT:vvdesc NB_MSG.

(*after occurs immediately after before occurs.*)
Inductive ImmAfter (after:@KOAction NB_MSG PLT) (before:@KOAction NB_MSG PLT)
  : @KTrace NB_MSG PLT -> Prop :=
| IA_nil : ImmAfter after before nil
(*An action not matching before is added*)
| IA_nB : forall before' tr, ImmAfter after before tr ->
                             ~AMatch before before' ->
                             ImmAfter after before (before'::tr)
(*An action matching before is added*)
| IA_B : forall before' after' tr, ImmAfter after before tr ->
                                   AMatch after after' ->
                                   ImmAfter after before (after'::before'::tr).

(*before occurs immediate before after occurs*)
Inductive ImmBefore (before:@KOAction NB_MSG PLT) (after:@KOAction NB_MSG PLT)
  : @KTrace NB_MSG PLT -> Prop :=
| IB_nil : ImmBefore before after nil
(*An action not matching after is added*)
| IB_nA : forall after' tr, ImmBefore before after tr ->
                            ~AMatch after after' ->
                            ImmBefore before after (after'::tr)
(*An action matching after is added*)
| IB_A : forall after' before' tr, ImmBefore before after tr ->
                                   AMatch before before' ->
                                   ImmBefore before after (after'::before'::tr).

Inductive Release (past:@KOAction NB_MSG PLT) (future:@KOAction NB_MSG PLT)
  : @KTrace NB_MSG PLT -> Prop :=
| R_nil : Release past future nil
| R_not_future : forall act tr, Release past future tr ->
                                ~AMatch future act ->
                                Release past future (act::tr)
| R_future : forall act tr, Release past future tr ->
                            (exists past', In past' tr /\
                                           AMatch past past') ->
                            Release past future (act::tr).

End PolLang.
