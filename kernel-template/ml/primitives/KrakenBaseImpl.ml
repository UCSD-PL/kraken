(*
 * UTILITIES
 *)

let mkstr =
  Printf.sprintf

let null =
  Char.chr 0

let mkbuf n =
  String.make n null

(* explode : string -> char list *)
let explode s =
  let rec loop i l =
    if i < 0 then
      l
    else
      loop (i - 1) (s.[i] :: l)
  in
  loop (String.length s - 1) []

(* implode : char list -> string *)
let implode cs =
  let s = mkbuf (List.length cs) in
  let rec loop i = function
    | c::cs' -> begin
        s.[i] <- c;
        loop (i + 1) cs'
    end
    | [] ->
        s
  in
  loop 0 cs

(* decode bytes of str to a num *)
let str_num s =
  List.fold_left (fun acc c -> acc * 256 + Char.code c) 0 (explode s)

(* encode bytes of num to a str *)
let num_str n =
  let rec loop acc n =
    if n < 256 then
      Char.chr n :: acc
    else
      loop (Char.chr (n mod 256) :: acc) (n / 256)
  in
  if n < 0 then
    failwith (mkstr "ERROR: num_str got negative arg %d" n)
  else
    implode (List.rev (loop [] n))

(* prepend fill to s until it reaches len *)
let rec pad_front fill len s =
  if String.length s < len then
    pad_front fill len (Char.escaped fill ^ s)
  else
    s

(*
 * LOGGING
 *)

let log msg =
  ()

(*
 * IO OPERATIONS
 *)

(* dummy args represent trace *)

type chan = Unix.file_descr

let recvN c  _ =
  let b = mkbuf 4 in
  let n = Unix.read c b 0 4 in
  if n <> 4 then
    failwith (mkstr "ERROR: recvN only read %d bytes instead of 4" n)
  else begin
    let x = str_num b in
    log (mkstr "recvN got '%s' which decoded to %d" b x);
    x
  end

let recvS c bsize _ =
  let b = mkbuf bsize in
  let n = Unix.read c b 0 bsize in
  if n <> bsize then
    failwith (mkstr "ERROR: recvS only read %d bytes insted of %d" n bsize)
  else begin
    log (mkstr "recvS got '%s'" b);
    b
  end

let sendN c n _ =
  let b = pad_front null 4 (num_str n) in
  if String.length b <> 4 then
    failwith (mkstr "ERROR: sendN got oversized arg %d" n)
  else begin
    let n = Unix.write c b 0 4 in
    if n <> 4 then
      failwith (mkstr "ERROR: sendN only wrote %d bytes instead of 4" n)
    else
      log (mkstr "sendN put %d which encoded to '%s'" n (String.escaped b))
  end

let sendS c b _ =
  let bsize = String.length b in
  let n = Unix.write c b 0 bsize in
  if n <> bsize then
    failwith (mkstr "ERROR: sendS tried to put '%s' but only wrote %d bytes insted of %d" b n bsize)
  else
    log (mkstr "sendS put '%s'" b)
