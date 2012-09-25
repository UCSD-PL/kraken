let int_of_num n =
  Char.code (MlCoq.char_of_ascii n)

let kroot =
  try
    Sys.getenv "KROOT"
  with Not_found ->
    failwith "KROOT environment variable not set"

let prog_path p =
  List.fold_left
    Filename.concat
    ""
    [kroot; "client"; p]

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
let int_of_fd : Unix.file_descr -> int =
  Obj.magic

let string_of_fd fd =
  string_of_int (int_of_fd fd)

(*
 * PRIMITIVES
 *)

type chan = Unix.file_descr

let chan_eq c1 c2 =
  c1 = c2

type fdesc = Unix.file_descr

let exec prog _ =
  let prog = MlCoq.string_of_str prog in
  let p, c = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  match Unix.fork () with
  | 0 -> (* child *) begin
      Unix.close p;
      let p = prog_path prog in
      Unix.handle_unix_error (fun _ ->
        Unix.execv p [|p; string_of_fd c|]) ()
  end
  | cpid -> (* parent *) begin
      Unix.close c;
      p
  end

let call prog arg _ =
  let prog = MlCoq.string_of_str prog in
  let arg = MlCoq.string_of_str arg in
  let r, w = Unix.pipe () in
  match Unix.fork () with
  | 0 -> (* child *) begin
      Unix.close r;
      let p = prog_path prog in
      Unix.handle_unix_error (fun _ ->
        Unix.execv p [|p; arg; string_of_fd w|]) ()
  end
  | cpid -> (* parent *) begin
      Unix.close w;
      r (* TODO who closes r ? *)
  end

let select chans _ =
  let r, _, _ =
    Unix.handle_unix_error (fun _ ->
      Unix.select chans [] [] (-1.0)) ()
  in
  List.hd r

let recv c n _ =
  let n = int_of_num n in
  let s = String.make n (Char.chr 0) in
  let r = 
    Unix.handle_unix_error (fun _ ->
      Unix.recv c s 0 n []) ()
  in
  if r <> n then
    failwith "recv - wrong # of bytes"
  else
    MlCoq.str_of_string s

let send c s _ =
  let s = MlCoq.string_of_str s in
  let n = String.length s in
  let w =
    Unix.handle_unix_error (fun _ ->
      Unix.send c s 0 n []) ()
  in
  if w <> n then
    failwith "send - wrong # of bytes"
  else
    ()

external recv_fd_native : chan -> fdesc = "recv_fd_native"
let recv_fd c _ = recv_fd_native c

external send_fd_native : chan -> fdesc -> unit = "send_fd_native"
let send_fd c fd _ = send_fd_native c fd
