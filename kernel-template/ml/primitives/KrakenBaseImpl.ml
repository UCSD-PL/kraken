let (|>) x f =
  f x

(*
 * ML <-> Coq
 *)

let bits_of_ascii = function
  | MlCoq.Ascii (a1, a2, a3, a4, a5, a6, a7, a8) ->
      [a8; a7; a6; a5; a4; a3; a2; a1]

let ascii_of_bits = function
  | [a8; a7; a6; a5; a4; a3; a2; a1] ->
      MlCoq.Ascii (a1, a2, a3, a4, a5, a6, a7, a8)
  | _ ->
      failwith "ascii_of_bits"

let char_of_bits b =
  b |> List.map (function true -> 1 | false -> 0)
    |> List.fold_left (fun n b -> 2 * n + b) 0
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
  ()

type chan =
  Unix.file_descr

let recv c n _ =
  let n = int_of_num n in
  let s = String.make n (Char.chr 0) in
  let r = Unix.read c s 0 n in
  if r <> n then
    failwith (mkstr "recv expected %d but got %d" n r)
  else begin
    log (mkstr "recv '%s'" (String.escaped s));
    str_of_string s
  end

let send c s _ =
  let s = string_of_str s in
  let n = String.length s in
  let w = Unix.write c s 0 n in
  if w <> n then
    failwith (mkstr "send expected %d but put %d" n w)
  else begin
    log (mkstr "send '%s'" (String.escaped s))
  end
