open Common

let usage () =
  print "
!!! You probably hit a bug in the kraken.sh driver script.
!!! This usage info is for the core compiler which should not be run directly.

Usage: kraken [options] input.krn

Compile a Kraken kernel spec to Coq code and proofs and client libraries.

In options below X \\in {message, kernel, kprop, pylib, clib-h, clib-c}.

OPTIONS:

  -h, --help             print this usage information
  --template X FILE      read template for X from FILE
  --instance X FILE      write instatiation of X to FILE

A template and instance for message, kernel, and kprop must be provided.
Libraries are optional and will only be produced if their respective template
and instance options are provided. A template should always be provided with a
corresponding instance and vice versa.

EXAMPLE:

To compile kernel.krn using message template/instatiation of MT.v/M.v and kernel
template/instantiation of KT.v/K.v and kprop template/instantiation of PT.v/P.v,
while producing no client library code, run:

  kraken \\
    --template message MT.v \\
    --instance message M.v  \\
    --template kernel  KT.v \\
    --instance kernel  K.v  \\
    --template kprop   PT.v \\
    --instance kprop   P.v  \\
    kernel.krn

!!! You probably hit a bug in the kraken.sh driver script.
!!! This usage info is for the core compiler which should not be run directly.
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
  | "message" | "kernel" | "kprop" | "pylib" | "clib-h" | "clib-c" -> true
  | _ -> false

let parse_args () =
  let rec loop = function
    | "-h" :: _ | "-help" :: _ | "--help" :: _ ->
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
  else begin
    loop args;
    (* ensure required args are set *)
    List.iter (fun x -> ignore (get_flag x))
      [ "input"
      ; "t-message" ; "i-message"
      ; "t-kernel"  ; "i-kernel"
      ; "t-kprop"   ; "i-kprop"
      ]
  end

let desugar_let k =
  let open Kernel in
  let desugar p =
    let rec desugar_aux bindings = function
    | Nop -> (Nop, bindings)
    | Seq (cmd, p) ->
      match cmd with
      | Assign (id, expr) ->
        desugar_aux (GenKernel.set_var bindings id expr) p
      | Send (c, msg) ->
        let c = Gen.coq_of_expr (GenKernel.lkup_var bindings c) in
        let msg = GenKernel.lkup_msg_expr bindings msg in
        let (prog, bindings) = desugar_aux bindings p in
        (Seq (Send(c, msg), prog), bindings)
      | Call (res, f, arg) ->
        let (prog, bindings) = desugar_aux bindings p in
        (Seq (Call (res, f, arg), prog), bindings)
      | Spawn (res, comp) ->
        let (prog, bindings) = desugar_aux bindings p in
        (Seq (Spawn (res, comp), prog), bindings)
      | Connect (soc, url) ->
        let (prog, bindings) = desugar_aux bindings p in
        (Seq (Connect (soc, url), prog), bindings)
    in desugar_aux [] (fst p)
  in
  let open Kernel in
  { k with
    init = desugar k.init
  ; exchange = (
      let (c, chll) = k.exchange in
      let chll =
        List.map (fun (c, hl) ->
          (c,
            List.map (fun h ->
              { h with responds =
                List.map (fun cp ->
                  { cp with program = desugar cp.program }
                ) h.responds
              }
            ) hl
          )
        ) chll
      in
      (c, chll)
    )
  }

let parse_kernel f =
  f |> readfile
    |> Lexing.from_string
    |> Parse.kernel Lex.token
    |> desugar_let

(* for catg: read template, rewrite with subs, write instance *)
let instantiate catg (subs : (Str.regexp * string) list) =
  if flag_is_set ("t-" ^ catg) then
    get_flag ("t-" ^ catg)
      |> readfile
      |> List.fold_right (uncurry Str.global_replace) subs
      |> writefile (get_flag ("i-" ^ catg))

let main () =
  parse_args ();
  let k = parse_kernel (get_flag "input") in
  List.iter (uncurry instantiate)
    [ "message" , GenMessage.subs k
    ; "kernel"  , GenKernel.subs k
    ; "kprop"   , GenKProp.subs k
    ; "pylib"   , GenPyLib.subs k
    ; "clib-h"  , GenCLib.subs_h k
    ; "clib-c"  , GenCLib.subs_c k
    ]

let _ =
  main ()
