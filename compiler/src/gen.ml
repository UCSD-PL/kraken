open Common
open Kernel

(* code common to at least 2 generators *)

let lcat l =
  l |> List.filter ((<>) "")
    |> String.concat "\n"

let fmt l f =
  l |> List.map f
    |> lcat

let coq_of_typ = function
  | Num   -> "num"
  | Str   -> "str"
  | Fdesc -> "fdesc"
  | Chan  -> "tchan"

let rec coq_of_expr = function
  | Var id -> id
  | NumLit i -> mkstr "(Num \"%03d\")" i
  | StrLit s -> mkstr "(str_of_string \"%s\")" s
  | Plus (a, b) ->
    mkstr "(num_of_nat ((nat_of_num (%s)) + (nat_of_num (%s))))"
      (coq_of_expr a) (coq_of_expr b)

let coq_of_args m =
  m.payload
    |> mapi (fun i _ -> mkstr "p%d" i)
    |> String.concat " "
