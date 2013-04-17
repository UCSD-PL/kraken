Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexFin.

Module Type SystemFeaturesInterface.
  Parameter NB_MSG   : nat.
  Parameter PAYD     : vvdesc NB_MSG.
  Parameter COMPT    : Set.
  Parameter COMPTDEC : forall (x y : COMPT), decide (x = y).
  Parameter COMPS    : COMPT -> compd.
  Parameter IENVD    : vdesc.
  Parameter KSTD     : vdesc.
End SystemFeaturesInterface.

Module MkLanguage (Import SF : SystemFeaturesInterface).
  Definition sendall  := SendAll  PAYD COMPT COMPS KSTD.
  Definition spawn := Spawn PAYD COMPT COMPS KSTD.
  Definition stupd := StUpd PAYD COMPT COMPS KSTD.
  Definition stvar {cc envd m} v :=
    Term (hdlr_term PAYD COMPT COMPS KSTD cc m envd) (StVar _ _ _ _ _ _ _ v).
  Definition slit {cc envd m} v :=
    Term (hdlr_term PAYD COMPT COMPS KSTD cc m envd) (Base _ _ _ _ _ _ _ (SLit _ v)).
  Definition nlit {cc envd m} v :=
    Term (hdlr_term PAYD COMPT COMPS KSTD cc m envd) (Base _ _ _ _ _ _ _ (NLit _ v)).
  Definition cfd {cc envd m} :=
    Term (hdlr_term PAYD COMPT COMPS KSTD cc m envd) (CFd _ _ _ _ _ _ _).
  Definition i_slit v := Term (base_term IENVD) (SLit _ v).
  Definition i_nlit v := Term (base_term IENVD) (NLit _ v).
End MkLanguage.

Module Type SpecInterface.
  Include SystemFeaturesInterface.
  Parameter INIT : init_prog PAYD COMPT COMPS KSTD IENVD.
  Parameter HANDLERS : handlers PAYD COMPT COMPS KSTD.
End SpecInterface.

Module MkMain (Import S : SpecInterface).
  Definition main :=
    @main _ PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS.
End MkMain.

Fixpoint mk_vdesc' l : vdesc' (List.length l) :=
  match l with
  | nil     => tt
  | x :: xs => (x, mk_vdesc' xs)
  end.

Definition mk_vdesc l : vdesc := existT _ (List.length l) (mk_vdesc' l).

Fixpoint mk_vvdesc (l : list (string * list desc)) : vvdesc (List.length l) :=
  match l with
  | nil          => tt
  | (_, x) :: xs => (mk_vdesc x, mk_vvdesc xs)
  end.

Definition mk_compd name cmd args conf :=
  {| compd_name := str_of_string name
   ; compd_cmd  := str_of_string cmd
   ; compd_args := List.map str_of_string args
   ; compd_conf := conf
   |}.

Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).

Definition cast_m_expr
  {NB_MSG COMPT COMPS} {PAYD : vvdesc NB_MSG} {KSTD envd} {m : msg PAYD} {cc t p d}
  (EQ : Build_msg PAYD t p = m)
  (e : expr (hdlr_term PAYD COMPT COMPS KSTD cc (Build_msg PAYD t p) envd) d)
  : expr (hdlr_term PAYD COMPT COMPS KSTD cc m envd) d
  :=
  match EQ in _ = _m return expr (hdlr_term _ _ _ _ _ _m _) _ with
  | Logic.eq_refl => e
  end.

Definition mvar
  {NB_MSG COMPT COMPS} {PAYD : vvdesc NB_MSG} {KSTD envd} {m : msg PAYD} {cc t p}
  (EQ : Build_msg PAYD t p = m) i :=
  cast_m_expr EQ (Term _ (MVar PAYD COMPT COMPS KSTD cc (Build_msg PAYD t p) envd i)).
