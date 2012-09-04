let (|>) x f =
  f x

let tick =
  ref 0

let tock =
  incr tick;
  !tick

let print =
  Printf.printf

let mkstr =
  Printf.sprintf

let range a b =
  let rec loop acc i =
    if i < b then
      loop (i::acc) (i+1)
    else
      List.rev acc
  in
  loop [] a

let explode s =
  let rec loop i l =
    if i < 0 then
      l
    else
      loop (i - 1) (s.[i] :: l)
  in
  loop (String.length s - 1) []

let bits n =
  let rec loop i acc n =
    if i = 0 then
      acc
    else if n land 1 = 0 then
      loop (i - 1) (false :: acc) (n lsr 1)
    else
      loop (i - 1) (true :: acc) (n lsr 1)
  in
  loop 32 [] n

let rec take n l =
  match n, l with
  | 0, _ -> []
  | _, [] -> failwith "take"
  | n, x :: xs -> x :: take (n - 1) xs

let rec drop n l =
  match n, l with
  | 0, l -> l
  | _, [] -> failwith "drop"
  | n, x :: xs -> drop (n - 1) xs

let readline f =
  try
    Some (input_line f)
  with End_of_file ->
    None

let readlines file =
  let f = open_in file in
  let rec loop ls =
    match readline f with
    | Some l ->
        loop (l::ls)
    | None ->
        close_in f;
        List.rev ls
  in
  loop []

let file_str f =
  String.concat "\n" (readlines f)

let str_file file s =
  let f = open_out file in
  output_string f s;
  close_out f
