open Common
open Kernel

(* code common to at least 2 generators *)

let lcat l =
  l |> List.filter ((<>) "")
    |> String.concat "\n"

let fmt l f =
  l |> List.map f
    |> lcat

let fmti l f =
  l |> mapi f
    |> lcat

let coq_of_typ = function
  | Num   -> "num"
  | Str   -> "str"
  | Fdesc -> "fdesc"
  | Chan  -> "tchan"

(* 255 becomes the string (Num ("000", "001")) *)
let coq_num_of_int i =
  let l = i mod 256 in
  let h = i / 256 in
  mkstr "(Num (\"%03d\", \"%03d\"))" l h

let rec coq_of_expr = function
  | Var id -> id
  | NumLit i -> coq_num_of_int i
  | StrLit s -> mkstr "(str_of_string \"%s\")" s
  | Plus (a, b) ->
    mkstr "(num_of_nat ((nat_of_num (%s)) + (nat_of_num (%s))))"
      (coq_of_expr a) (coq_of_expr b)

let coq_of_args m =
  m.payload
    |> mapi (fun i _ -> mkstr "p%d" i)
    |> String.concat " "
