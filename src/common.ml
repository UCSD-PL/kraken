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
