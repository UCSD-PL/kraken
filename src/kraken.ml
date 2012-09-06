open Common

let usage () =
  print "
  Usage: kraken [OPTIONS] <input.krn>

  Generate Coq code and proofs from a Kraken kernel spec.

  OPTIONS:
    -h, --help        print this usage information
    --pylib PYLIB     write Python message library to file PYLIB
    --turn TURN       write Coq turn module to file TURN
  ";
  exit 1

let flags : (string * string) list ref =
  ref []

let set_flag f v =
  flags := (f, v) :: !flags

let get_flag f =
  try
    List.assoc f !flags
  with Not_found ->
    failwith (mkstr "Flag '%s' not set." f)

(* default flag values *)
let _ =
  set_flag "input" "";
  set_flag "pylib" "kraken_msg_lib.py";
  set_flag "turn" "Turn.v"

let parse_args () =
  let rec loop = function
    | "-h" :: t | "--help" :: t ->
        usage ()
    | "--pylib" :: f :: t ->
        set_flag "pylib" f;
        loop t
    | "--turn" :: f :: t ->
        set_flag "turn" f;
        loop t
    | i :: t ->
        set_flag "input" i;
        loop t
    | [] ->
        ()
  in
  loop (Array.to_list Sys.argv)

let parse_spec f =
  f |> file_str
    |> Lexing.from_string
    |> Parse.spec Lex.token

let main () =
  parse_args ();
  let s = parse_spec (get_flag "input") in
  str_file (get_flag "turn") (Spec.spec_coq s);
  str_file (get_flag "pylib") (Spec.spec_pylib s)

let _ =
  main ()
