let explode s =
  let rec loop i cs =
    if i < 0 then
      cs
    else
      loop (i - 1) (s.[i] :: cs)
  in
  loop (String.length s - 1) []

let implode cs =
  let s = String.create (List.length cs) in
  let rec loop i = function
    | c :: cs' ->
        s.[i] <- c;
        loop (i + 1) cs'
    | [] -> s
  in
  loop 0 cs

(* NOTE MlCoq.Ascii has least significant bit first *)

let char_of_ascii = function
  | MlCoq.Ascii (b1, b2, b3, b4, b5, b6, b7, b8) ->
      Char.chr (
        (if b1 then   1 else 0) lor
        (if b2 then   2 else 0) lor
        (if b3 then   4 else 0) lor
        (if b4 then   8 else 0) lor
        (if b5 then  16 else 0) lor
        (if b6 then  32 else 0) lor
        (if b7 then  64 else 0) lor
        (if b8 then 128 else 0))

let ascii_of_char c =
  let c = Char.code c in
  MlCoq.Ascii
    ( c land   1 = 0
    , c land   2 = 0
    , c land   4 = 0
    , c land   8 = 0
    , c land  16 = 0
    , c land  32 = 0
    , c land  64 = 0
    , c land 128 = 0
    )

let string_of_str s =
  implode (List.map char_of_ascii s)

let str_of_string s =
  List.map ascii_of_char (explode s)

let int_of_num n =
  Char.code (char_of_ascii n)

(*
 * PRIMITIVES
 *)

type chan =
  Unix.file_descr

(* TODO *)
let exec s _ =
  Unix.stdin

let recv c n _ =
  let n = int_of_num n in
  let s = String.make n (Char.chr 0) in
  let r = Unix.recv c s 0 n [] in
  if r <> n then
    failwith "recv"
  else
    str_of_string s

let send c s _ =
  let s = string_of_str s in
  let n = String.length s in
  let w = Unix.send c s 0 n [] in
  if w <> n then
    failwith "send"
  else
    ()

(*
 * TEMPORARY FOR TESTING
 *)

(* Forked components need to know which file descriptor to use for
 * communicating with the kernel.
 *
 * Unfortunately, Unix.file_descr is declared as an abstract type in the
 * Unix module signature, which hides its implementation and thus prevents
 * sending some representation of a file descriptor to a forked component.
 *
 * This function exposes the implementation of Unix.file_descr as an int,
 * which in turn enables passing a representation of a file descriptor to
 * forked components.
 *)
let int_of_file_descr : Unix.file_descr -> int =
  Obj.magic

let mkchan () =
  let (p, c) = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  match Unix.fork () with
  | 0 -> (* child *)
      let cmd = Sys.getenv "KRAKEN_TEST" in
      Unix.execv cmd [|cmd; mkstr "%d" (int_of_file_descr c)|]
  | x -> (* parent *)
      p
