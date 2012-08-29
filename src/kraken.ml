open Common

let parse f =
  f |> file_str
    |> Lexing.from_string
    |> Parse.spec Lex.token

let main () =
  Sys.argv.(1)
    |> parse
    |> Spec.spec_coq
    |> print "%s"

let _ =
  main ()
