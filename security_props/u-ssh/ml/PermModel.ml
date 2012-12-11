open BinInt
open BinPos
open Datatypes
open QArith_base
open Qcanon

type perm = coq_Qc

(** val coq_Qc0 : coq_Qc **)

let coq_Qc0 =
  coq_Q2Qc { coq_Qnum = Z0; coq_Qden = Coq_xH }

(** val top : perm **)

let top =
  coq_Q2Qc { coq_Qnum = Z0; coq_Qden = Coq_xH }

(** val compatibleb : perm -> perm -> bool **)

let compatibleb p1 p2 =
  let p1pos = coq_Qle_bool { coq_Qnum = Z0; coq_Qden = Coq_xH } (this p1) in
  let p2pos = coq_Qle_bool { coq_Qnum = Z0; coq_Qden = Coq_xH } (this p2) in
  negb
    (if if p1pos then p2pos else false
     then true
     else if if p1pos then true else p2pos
          then negb
                 (coq_Qle_bool { coq_Qnum = Z0; coq_Qden = Coq_xH }
                   (this (coq_Qcplus p1 p2)))
          else false)

(** val perm_plus : perm -> perm -> perm option **)

let perm_plus p1 p2 =
  if compatibleb p1 p2 then Some (coq_Qcplus p1 p2) else None

(** val perm_plus_compat : perm -> perm -> perm **)

let perm_plus_compat p1 p2 =
  coq_Qcplus p1 p2

type permo = perm option

(** val permo_plus : permo -> permo -> permo **)

let permo_plus p1 p2 =
  match p1 with
  | Some p1' ->
    (match p2 with
     | Some p2' -> perm_plus p1' p2'
     | None -> None)
  | None -> None

(** val topo : permo **)

let topo =
  Some top

