open BinInt
open BinPos
open Datatypes
open QArith_base
open Qcanon

type perm = coq_Qc

val coq_Qc0 : coq_Qc

val top : perm

val compatibleb : perm -> perm -> bool

val perm_plus : perm -> perm -> perm option

val perm_plus_compat : perm -> perm -> perm

type permo = perm option

val permo_plus : permo -> permo -> permo

val topo : permo

