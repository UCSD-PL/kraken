(* NOTE least significant bit first *)
type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type nat =
  | O
  | S of nat
