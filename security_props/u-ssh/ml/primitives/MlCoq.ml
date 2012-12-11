(* NOTE least significant bit first *)
type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type nat =
  | O
  | S of nat

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

let char_of_ascii = function
  | Ascii (b1, b2, b3, b4, b5, b6, b7, b8) ->
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
  Ascii
    ( c land   1 <> 0
    , c land   2 <> 0
    , c land   4 <> 0
    , c land   8 <> 0
    , c land  16 <> 0
    , c land  32 <> 0
    , c land  64 <> 0
    , c land 128 <> 0
    )

let string_of_str s =
  implode (List.map char_of_ascii s)

let str_of_string s =
  List.map ascii_of_char (explode s)
