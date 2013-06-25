Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexHVec.
Require Import ReflexIO.

Module Type SystemFeaturesInterface.
  Parameter NB_MSG   : nat.
  Parameter PAYD     : vvdesc NB_MSG.
  Parameter COMPT    : Set.
  Parameter COMPTDEC : forall (x y : COMPT), decide (x = y).
  Parameter COMPS    : COMPT -> compd.
  Parameter IENVD    : vcdesc COMPT.
  Parameter KSTD     : vcdesc COMPT.
End SystemFeaturesInterface.

Module MkLanguage (Import SF : SystemFeaturesInterface).
  Instance SDenoted_cdesc : SDenoted (cdesc COMPT) := SDenoted_cdesc COMPT COMPS.
  Definition seq {envd term} := Seq PAYD COMPT COMPS KSTD envd term.
  Definition nop {envd term} := Nop PAYD COMPT COMPS KSTD envd term.
  Definition ite {envd term} := Ite PAYD COMPT COMPS KSTD envd term.
  Definition send {envd term ct} := Reflex.Send PAYD COMPT COMPS KSTD envd term ct.
  Definition sendall := SendAll PAYD COMPT COMPS KSTD.
  Definition spawn := Spawn PAYD COMPT COMPS KSTD.
  Definition stupd := StUpd PAYD COMPT COMPS KSTD.
  Definition stvar {cc envd m} v :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD envd cc m) (StVar _ _ _ _ _ _ _ v).
  Definition envvar {cc m} envd i :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD envd cc m)
         (Base _ _ _ _ _ _ _ (Var _ envd i)).
  Definition slit {cc envd m} v :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD envd cc m) (Base _ _ _ _ _ _ _ (SLit _ _ v)).
  Definition nlit {cc envd m} v :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD envd cc m) (Base _ _ _ _ _ _ _ (NLit _ _ v)).
  Definition ccomp {cc envd m} :=
    Term COMPT (hdlr_term PAYD COMPT COMPS KSTD envd cc m) (CComp _ _ _ _ _ _ _).
  Definition i_slit v := Term COMPT (base_term _ IENVD) (SLit _ _ v).
  Definition i_nlit v := Term COMPT (base_term _ IENVD) (NLit _ _ v).
  Definition mk_comp_pat := Build_comp_pat COMPT COMPS.

(*
  Definition comp_fd {envd ct} ce (*{ct : COMPT} (x : sigT (fun c => comp_type COMPT COMPS c = ct))*)
    := CompFd COMPT envd ct ce.*)
  Definition comp_conf {ct : COMPT} (x : sigT (fun c => comp_type COMPT COMPS c = ct))
  : s[[ comp_conf_desc COMPT COMPS ct ]]
    :=
      match projT2 x in _ = _ct return s[[ comp_conf_desc COMPT COMPS _ct ]] with
      | Logic.eq_refl => comp_conf COMPT COMPS (projT1 x)
      end.

  Definition i_env_ith s i :=
    shvec_ith (n := projT1 IENVD) (sdenote_cdesc COMPT COMPS) (projT2 IENVD)
              (init_env PAYD COMPT COMPS KSTD IENVD s) i.
  Notation "s ## i" := (i_env_ith s i) (at level 0) : ienv.
  Delimit Scope ienv with ienv.

  Definition env_ith {ENVD : vcdesc COMPT} s i :=
    shvec_ith (n := projT1 ENVD) (sdenote_cdesc COMPT COMPS) (projT2 ENVD)
              (hdlr_env PAYD COMPT COMPS KSTD ENVD s) i.
  Notation "s ## i" := (env_ith s i) (at level 0) : env.
  Delimit Scope env with env.

  Definition kst_ith s i :=
    shvec_ith (n := projT1 KSTD) (sdenote_cdesc COMPT COMPS) (projT2 KSTD)
              (kst PAYD COMPT COMPS KSTD s) i.
  Notation "s ## i" := (kst_ith s i) (at level 0) : kst.
  Delimit Scope kst with kst.

  Definition eq {term d} e1 e2 :=
    BinOp COMPT term
          (Eq _ d) e1 e2.

  Definition splitfst term c s :=
    UnOp COMPT term (SplitFst _ c) s.

  Definition splitsnd term c s :=
    UnOp COMPT term (SplitSnd _ c) s.

  Definition mvar
  {envd} (t : fin NB_MSG) {ct} i :=
  (Term COMPT _ (MVar PAYD COMPT COMPS KSTD envd ct t i)).

  Definition cconf
  {envd} {t : fin NB_MSG} ct i :=
  (Term COMPT _ (CConf PAYD COMPT COMPS KSTD envd ct t i)).

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

Fixpoint mk_vcdesc' {COMPT} l : vcdesc' COMPT (List.length l) :=
  match l with
  | nil     => tt
  | x :: xs => (x, mk_vcdesc' xs)
  end.

Definition mk_vcdesc {COMPT} l : vcdesc COMPT := existT _ (List.length l) (mk_vcdesc' l).

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

Notation "<< n & e >>" := (existT _ n e)
 (n at level 59, e at level 39) : hdlr.
Notation "[[ e : c ]]" := (existT _ e c)
 (c at level 59, e at level 39) : hdlr.

Delimit Scope fin_scope with fin.

Notation "0"  := (None) : fin_scope.
Notation "1"  := (Some (None)) : fin_scope.
Notation "2"  := (Some (Some None)) : fin_scope.
Notation "3"  := (Some (Some (Some None))) : fin_scope.
Notation "4"  := (Some (Some (Some (Some None)))) : fin_scope.
Notation "5"  := (Some (Some (Some (Some (Some None))))) : fin_scope.
Notation "6"  := (Some (Some (Some (Some (Some (Some None)))))) : fin_scope.
Notation "7"  := (Some (Some (Some (Some (Some (Some (Some None))))))) : fin_scope.
Notation "8"  := (Some (Some (Some (Some (Some (Some (Some (Some None)))))))) : fin_scope.
Notation "9"  := (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))) : fin_scope.
Notation "10" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))) : fin_scope.
Notation "11" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))) : fin_scope.
Notation "12" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))) : fin_scope.
Notation "13" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))) : fin_scope.
Notation "14" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))) : fin_scope.
Notation "15" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))))) : fin_scope.
Notation "16" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))))) : fin_scope.
Notation "17" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))))))) : fin_scope.
Notation "18" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))))))) : fin_scope.
Notation "19" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))))))))) : fin_scope.
Notation "20" := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))))))))) : fin_scope.