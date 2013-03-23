Require Import String.

Require Import Reflex.
Require Import ReflexBase.

Record spec :=
{ NB_MSG   : nat
; PAYD     : vvdesc NB_MSG
; IENVD    : vdesc
; KSTD     : vdesc
; COMPT    : Type
; COMPS    : COMPT -> comp
; INIT     : init_prog PAYD COMPT KSTD (init_msg PAYD) IENVD
; HANDLERS : handlers PAYD COMPT KSTD
}.

Definition mk_main (s : spec) :=
  @main _ (PAYD s) (COMPT s) (COMPS s) (KSTD s) (IENVD s) (INIT s) (HANDLERS s).

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

Definition mk_comp name cmd args :=
  {| comp_name := str_of_string name
   ; comp_cmd  := str_of_string cmd
   ; comp_args := List.map str_of_string args
   |}.

Notation " [ ] " := nil.
Notation " [ x ] " := (cons x nil).
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).

Definition cast_m_expr {NB_MSG} {PAYD : vvdesc NB_MSG} {KSTD envd} {m : msg PAYD} {t p d}
  (EQ : Build_msg PAYD t p = m) (e : expr PAYD KSTD (Build_msg PAYD t p) envd d)
  : expr PAYD KSTD m envd d
  :=
  match EQ in _ = _m return expr _ _ _m _ _ with
  | Logic.eq_refl => e
  end.

Definition mvar {NB_MSG} {PAYD : vvdesc NB_MSG} {KSTD envd} {m : msg PAYD} {t p}
  (EQ : Build_msg PAYD t p = m) i :=
  cast_m_expr EQ (MVar PAYD KSTD (Build_msg PAYD t p) envd i).
