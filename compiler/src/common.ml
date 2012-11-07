let (|>) x f = f x

let tick = ref 0
let tock () = incr tick; !tick

let print = Printf.printf
let mkstr = Printf.sprintf

let rec range a b =
  if a < b then
    a :: range (a + 1) b
  else
    []

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

let last_bits k n =
  let rec loop k bits n =
    if k <= 0 then
      bits
    else if n land 1 = 0 then
      loop (k - 1) (false :: bits) (n lsr 1)
    else
      loop (k - 1) (true :: bits) (n lsr 1)
  in
  loop k [] n

let rec take n l =
  if n = 0 then
    []
  else
    match l with
    | [] -> failwith "take"
    | x::xs -> x :: take (n - 1) xs

let rec drop n l =
  if n = 0 then
    l
  else
    match l with
    | [] -> failwith "drop"
    | _::xs -> drop (n - 1) xs

let curry (f: 'a * 'b -> 'c) : 'a -> 'b -> 'c =
  fun a b -> f (a, b)

let uncurry (f: 'a -> 'b -> 'c) : 'a * 'b -> 'c =
  fun (a, b) -> f a b

let rec remove_repeats = function
  | x :: y :: l ->
      if x = y then
        remove_repeats (y :: l)
      else
        x :: remove_repeats (y :: l)
  | _ as l -> l

let rec mapi_aux f i = function
  | [] -> []
  | x :: l -> f i x :: mapi_aux f (i + 1) l

let mapi f = mapi_aux f 0

(* WARNING does not maintain order *)
let uniq l =
  l |> List.sort compare
    |> remove_repeats

let rec remove a = function
  | [] ->
      failwith "remove"
  | x :: l' ->
      if x = a then
        l'
      else
        x :: remove a l'

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

let readfile f =
  String.concat "\n" (readlines f)

let writefile file s =
  let f = open_out file in
  output_string f s;
  close_out f

let writelines f ls =
  writefile f (String.concat "\n" ls)
