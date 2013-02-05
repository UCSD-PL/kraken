Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexVec.
Require Import ReflexHVec.

Inductive OptTag : Type :=
C_opttag : payload_desc -> OptTag.

Definition soptdenote_desc (d : desc) : Set :=
  option (sdenote_desc d).

Definition soptdenote_payload_desc' n (pt : payload_desc' n) : Set :=
  shvec soptdenote_desc pt.

Instance SOptDenoted_payload_desc : SDenoted OptTag :=
{ sdenote := fun opttag => match opttag with
                           | C_opttag pd =>
                             soptdenote_payload_desc' (projT1 pd) (projT2 pd)
                           end
}.

Section KOAction.

Context {NB_MSG:nat}.
Context {PLT:payload_desc_vec NB_MSG}.

Record opt_msg : Set :=
  { opt_tag : fin NB_MSG
  ; opt_pay : s[[ C_opttag (lkup_tag NB_MSG PLT opt_tag) ]]
  }.

(*Definition KTrace := KTrace NB_MSG PLT.*)
(*Definition KAction := KAction NB_MSG PLT.*)

Inductive KOAction : Set :=
| KOExec   : option str -> option (list str) -> option fd -> KOAction
| KOCall   : option str -> option (list str) -> option fd -> KOAction
| KOSelect : option (list fd) -> option fd -> KOAction
| KOSend   : option fd -> option opt_msg -> KOAction
| KORecv   : option fd -> option opt_msg -> KOAction
| KOBogus  : option fd -> option num -> KOAction.

Inductive Regexp : Type :=
| RE_Atom   : KOAction -> Regexp
| RE_NAtom  : KOAction -> Regexp
| RE_Any    : Regexp
| RE_Alt    : Regexp -> Regexp -> Regexp
| RE_Star   : Regexp -> Regexp
| RE_Concat : Regexp -> Regexp -> Regexp.

Definition argMatch {T:Type} (opt:option T) (arg:T) : Prop :=
  match opt with
  | None   => True
  | Some t => t = arg
  end.

Fixpoint unpackedPLMatch n (pd:payload_desc' n)
                           (opt_pl:soptdenote_payload_desc' n pd)
                           (pl:sdenote_payload_desc' n pd) : Prop :=
  match n as _n
  return forall (pd' : payload_desc' _n),
         soptdenote_payload_desc' _n pd' ->
         sdenote_payload_desc' _n pd' ->
         Prop
  with
  | O => fun _ _ _ => True
  | S n' => fun pd opt_pl pl =>
    match pd as _pd return
      soptdenote_payload_desc' (S n') _pd ->
      sdenote_payload_desc' (S n') _pd ->
      Prop
    with
    | (t, pd') => fun opt_pl pl =>
      match opt_pl, pl with
      | (aopt, vopt), (a, v) =>
        argMatch aopt a /\ unpackedPLMatch n' pd' vopt v
      end
    end opt_pl pl
  end pd opt_pl pl.

Definition packedPLMatch
  (tag:fin NB_MSG)
  (opt_pay:s[[C_opttag (lkup_tag NB_MSG PLT tag)]])
  (pay:s[[lkup_tag NB_MSG PLT tag]]) : Prop :=
  match lkup_tag NB_MSG PLT tag as _l return
        s[[C_opttag _l ]] -> s[[ _l ]] -> Prop
  with
  | existT n pl' => unpackedPLMatch n pl'
  end opt_pay pay.

Definition msgMatch' (opt_pl:opt_msg) (pl:msg NB_MSG PLT) : Prop :=
  let opt_tag := (opt_tag opt_pl) in
  let tag := (tag NB_MSG PLT pl) in
  match fin_eq_dec tag opt_tag with
  | left H => match H in eq _ _tag return
                s[[C_opttag (lkup_tag NB_MSG PLT _tag)]] -> Prop
              with
              | eq_refl => fun opt_pay =>
                 packedPLMatch tag opt_pay (pay NB_MSG PLT pl)
              end (opt_pay opt_pl)
  | right H => False
  end.

Definition msgMatch (opt_pl:option opt_msg) (pl:msg NB_MSG PLT) : Prop :=
  match opt_pl with
  | None => True
  | Some opt_pl' => msgMatch' opt_pl' pl
  end.

Inductive AMatch : KOAction -> KAction NB_MSG PLT -> Prop :=
| AM_KExec : forall s s' ls ls' fd fd', argMatch s s' ->
                                        argMatch ls ls' ->
                                        argMatch fd fd' ->
                                        AMatch (KOExec s ls fd)
                                               (KExec _ _ s' ls' fd')
| AM_KCall : forall s s' ls ls' fd fd', argMatch s s' ->
                                        argMatch ls ls' ->
                                        argMatch fd fd' ->
                                        AMatch (KOCall s ls fd)
                                               (KCall _ _ s' ls' fd')
| AM_KSelect : forall lfd lfd' fd fd', argMatch lfd lfd' ->
                                       argMatch fd fd' ->
                                       AMatch (KOSelect lfd fd)
                                              (KSelect _ _ lfd' fd')
| AM_KSend : forall fd fd' msg msg', argMatch fd fd' ->
                                     msgMatch msg msg' ->
                                     AMatch (KOSend fd msg)
                                            (KSend _ _ fd' msg')
| AM_KRecv : forall fd fd' msg msg', argMatch fd fd' ->
                                     msgMatch msg msg' ->
                                     AMatch (KORecv fd msg)
                                            (KRecv _ _ fd' msg')
(**I don't know if this is the right thing to do for KBogus matching.
   It just checks if the message tags and fds are the same**)
| AM_KBogus : forall fd fd' optbtag bmsg, argMatch fd fd' ->
                                          argMatch optbtag (btag _ bmsg) ->
                                          AMatch (KOBogus fd optbtag)
                                                 (KBogus _ _ fd' bmsg).

Inductive RMatch : Regexp -> KTrace NB_MSG PLT -> Prop :=
| RM_Atom     : forall a a', AMatch a a' ->
                             RMatch (RE_Atom a) (a'::nil)
| RM_NAtom    : forall a a', ~ AMatch a a' ->
                             RMatch (RE_NAtom a) (a'::nil)
| RM_Any      : forall a, RMatch (RE_Any) (a::nil)
| RM_Alt      : forall re re' tr, RMatch re tr \/ RMatch re' tr ->
                                  RMatch (RE_Alt re re') tr
| RM_StarInit : forall re, RMatch (RE_Star re) nil
| RM_Star     : forall re tr tr', RMatch (RE_Star re) tr ->
                                  RMatch re tr' ->
                                  RMatch (RE_Star re) (tr' ++ tr)
| RM_Concat   : forall re re' tr tr', RMatch re tr ->
                                      RMatch re' tr' ->
                                      RMatch (RE_Concat re re') (tr ++ tr').

End KOAction.
