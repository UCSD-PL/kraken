Require Import Reflex.
Require Import ReflexBase.
Require Import ActionMatch.
Require Import List.

Section PolLang.

Context {NB_MSG:nat}.
Variable PAYD:vvdesc NB_MSG.

(*after occurs immediately after before occurs.*)
Inductive ImmAfter (after:KOAction PAYD) (before:KOAction PAYD)
  : KTrace PAYD -> Prop :=
| IA_nil : ImmAfter after before nil
(*An action not matching before is added*)
| IA_nB : forall before' tr, ImmAfter after before tr ->
                             ~AMatch PAYD before before' ->
                             ImmAfter after before (before'::tr)
(*An action matching before is added*)
| IA_B : forall before' after' tr, ImmAfter after before tr ->
                                   AMatch PAYD after after' ->
                                   ImmAfter after before (after'::before'::tr).

(*before occurs immediate before after occurs*)
Inductive ImmBefore (before:KOAction PAYD) (after:KOAction PAYD)
  : KTrace PAYD -> Prop :=
| IB_nil : ImmBefore before after nil
(*An action not matching after is added*)
| IB_nA : forall after' tr, ImmBefore before after tr ->
                            ~AMatch PAYD after after' ->
                            ImmBefore before after (after'::tr)
(*An action matching after is added*)
| IB_A : forall after' before' tr, ImmBefore before after tr ->
                                   AMatch PAYD before before' ->
                                   ImmBefore before after (after'::before'::tr).

Inductive Release (past:KOAction PAYD) (future:KOAction PAYD)
  : KTrace PAYD -> Prop :=
| R_nil : Release past future nil
| R_not_future : forall act tr, Release past future tr ->
                                ~AMatch PAYD future act ->
                                Release past future (act::tr)
| R_future : forall act tr, Release past future tr ->
                            (exists past', In past' tr /\
                                           AMatch PAYD past past') ->
                            Release past future (act::tr).

Inductive Disables (disabler:KOAction PAYD) (disablee:KOAction PAYD)
  : KTrace PAYD -> Prop :=
| D_nil : Disables disabler disablee nil
| D_not_disablee : forall act tr, Disables disabler disablee tr ->
                                  ~AMatch PAYD disablee act ->
                                  Disables disabler disablee (act::tr)
| D_disablee : forall act tr, Disables disabler disablee tr ->
                              (forall act', In act' tr ->
                                            ~AMatch PAYD disabler act') ->
                              Disables disabler disablee (act::tr).

End PolLang.
