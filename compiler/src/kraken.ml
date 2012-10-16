open Common

let usage () =
  print "

*** DO NOT RUN THIS PROGRAM DIRECTLY ***
***     USE THE KRAKEN.SH SCRIPT     ***

Usage: kraken [options] input.krn

Compile a Kraken kernel spec to Coq code and proofs and additionally produce
client libraries. Not intended to be run directly, should be invoked by
kraken.sh driver script.

In options below X \\in {kernel, pylib, clib-h, clib-c}.

OPTIONS:

  -h, --help             print this usage information
  --template X FILE      read template for X from FILE
  --instance X FILE      write instatiation of X to FILE

A template and instance for kernel must be provided. Libraries are optional and
will only be produced if their respective template and instance options are
provided. A template should always be provided with a corresponding instance and
vice versa.

EXAMPLE:

To compile kernel.krn using kernel template KT.v and write instantiation to K.v
while producing no client library code, one would run:

  kraken \\
    --template kernel KT.v \\
    --instance kernel K.v \\
    kernel.krn

!!! NOTE !!!

  The fact you are reading this probably means you hit a bug in the kraken.sh
  driver script. This usage information is for the core compiler which should
  only be run directly for development and debugging. In particular, this is NOT
  the usage information for the kraken.sh driver script. Hope that helps.

*** SERIOUSLY, READ ABOVE TEXT ***
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

let flag_is_set f =
  List.mem_assoc f !flags

let valid_catg = function
  | "kernel" | "pylib" | "clib-h" | "clib-c" -> true
  | _ -> false

let parse_args () =
  let rec loop = function
    | "-h" :: t | "-help" :: t | "--help" :: t ->
        usage ()
    | "--template" :: c :: v :: t ->
        if valid_catg c then begin
          set_flag ("t-" ^ c) v;
          loop t
        end else begin
          print "Invalid template category '%s'." c;
          usage ()
        end
    | "--instance" :: c :: v :: t ->
        if valid_catg c then begin
          set_flag ("i-" ^ c) v;
          loop t
        end else begin
          print "Invalid instance category '%s'." c;
          usage ()
        end
    | i :: t ->
        if Filename.check_suffix i ".krn" then begin
          set_flag "input" i;
          loop t
        end else begin
          print "Unrecognized option '%s'\n" i;
          usage()
        end
    | [] ->
        ()
  in
  let args =
    (* drop executable name *)
    List.tl (Array.to_list Sys.argv)
  in
  if args = [] then
    usage ()
  else
    loop args

let parse_kernel f =
  f |> readfile
    |> Lexing.from_string
    |> Parse.kernel Lex.token

(* read template t, rewrite with subs, write instance i *)
let instantiate t i subs =
  t |> readfile
    |> List.fold_right (uncurry Str.global_replace) subs
    |> writefile i

let main () =
  parse_args ();
  let k = parse_kernel (get_flag "input") in
  instantiate
    (get_flag "t-kernel")
    (get_flag "i-kernel")
    (GenCoq.coq_of_kernel_subs k);
  if flag_is_set "t-pylib" then
    instantiate
      (get_flag "t-pylib")
      (get_flag "i-pylib")
      (GenPy.pylib_subs k);
(*
  if flag_is_set "t-clib-h" then
    instantiate
      (get_flag "t-clib-h")
      (get_flag "i-clib-h")
      (GenC.clib_h_subs k);
  if flag_is_set "t-clib-c" then
    instantiate
      (get_flag "t-clib-c")
      (get_flag "i-clib-c")
      (GenC.clib_c_subs k)
*)
  ()

let _ =
  main ()
