let (|>) x f =
  f x

(*
 * ML <-> Coq
 *)

let bits_of_ascii = function
  | MlCoq.Ascii (b1, b2, b3, b4, b5, b6, b7, b8) ->
      [b8; b7; b6; b5; b4; b3; b2; b1]

let ascii_of_bits = function
  | [b8; b7; b6; b5; b4; b3; b2; b1] ->
      MlCoq.Ascii (b1, b2, b3, b4, b5, b6, b7, b8)
  | _ ->
      failwith "ascii_of_bits"

let char_of_bits l =
  if List.length l <> 8 then
    failwith "char_of_bits"
  else
    l |> List.map (function true -> 1 | false -> 0)
      |> List.fold_left (fun n b -> (n lsl 1) lor b) 0
      |> Char.chr

let bits_of_char c =
  let rec last_bits i acc n =
    if i = 0 then
      acc
    else
      last_bits (i - 1) (n land 1 :: acc) (n lsr 1)
  in
  c |> Char.code
    |> last_bits 8 []
    |> List.map (function 0 -> false | _ -> true)

let char_of_ascii a =
  a |> bits_of_ascii
    |> char_of_bits

let ascii_of_char c =
  c |> bits_of_char
    |> ascii_of_bits

let explode s =
  let rec loop i l =
    if i < 0 then l
    else loop (i - 1) (s.[i] :: l)
  in
  loop (String.length s - 1) []

let implode cs =
  let s = String.make (List.length cs) (Char.chr 0) in
  let rec loop i = function
    | c::cs' ->
        s.[i] <- c;
        loop (i + 1) cs'
    | [] -> s
  in
  loop 0 cs

let string_of_str s =
  s |> List.map char_of_ascii
    |> implode

let str_of_string s =
  s |> explode
    |> List.map ascii_of_char

let int_of_num n =
  Char.code (char_of_ascii n)

(*
 * PRIMITIVES
 *)

let mkstr =
  Printf.sprintf

let log msg =
  prerr_string msg

type chan =
  Unix.file_descr

let recv c n _ =
  let n = int_of_num n in
  let s = String.make n (Char.chr 0) in
  let r = Unix.recv c s 0 n [] in
  if r <> n then
    failwith (mkstr "recv expected %d but got %d" n r)
  else begin
    log (mkstr "recv '%s'" (String.escaped s));
    str_of_string s
  end

let send c s _ =
  let s = string_of_str s in
  let n = String.length s in
  let w = Unix.send c s 0 n [] in
  if w <> n then
    failwith (mkstr "send expected %d but put %d" n w)
  else begin
    log (mkstr "send '%s'" (String.escaped s))
  end

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
  let (p, c) =
    Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0
  in
  match Unix.fork () with
  | 0 -> (* child *)
      let cmd =
        "KRAKEN"
          |> Sys.getenv
          |> mkstr "%s/script/test-client.py"
      in
      Unix.execv
        cmd
        [|cmd; mkstr "%d" (int_of_file_descr c)|]
  | x -> (* parent *)
      Printf.printf "%d" x;
      p
