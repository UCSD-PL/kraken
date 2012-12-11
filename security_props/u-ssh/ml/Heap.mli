open Axioms
open BinInt
open BinPos
open Datatypes
open PermModel
open QArith_base
open Qcanon

type axiom_ptr = HeapImpl.axiom_ptr

type ptr = axiom_ptr

val axiom_ptr_eq_dec : ptr -> ptr -> bool

val ptr_eq_dec : ptr -> ptr -> bool

type hval = (dynamic, perm) prod

type heap = ptr -> hval option

val coq_val : hval -> dynamic

val frac : hval -> perm

val hval_plus : hval -> hval -> hval option

val hvalo_plus : hval option -> hval option -> hval option

val ofrac : hval option -> perm

val empty : heap

val singleton : ptr -> hval -> heap

val read : heap -> ptr -> hval option

val write : heap -> ptr -> hval -> heap

val free : heap -> ptr -> heap

val join : heap -> heap -> heap

