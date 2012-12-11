let int_of_num = function Datatypes.Coq_pair(l, h) ->
  let l = Char.code (MlCoq.char_of_ascii l) in
  let h = Char.code (MlCoq.char_of_ascii h) in
  l + h * 256

let kroot =
  try
    Sys.getenv "KROOT"
  with Not_found ->
    failwith "KROOT environment variable not set"

let prog_path p =
  if Filename.is_relative p then
    List.fold_left Filename.concat "" [kroot; "client"; p]
  else
    p

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
 * LOGGING
 *)

let _LOG =
  open_out (
    List.fold_left Filename.concat ""
      [kroot; "log"; "KERNEL-log"])

let log msg =
  output_string _LOG
    (Printf.sprintf "%15s @ %f || %s\n"
      "KERNEL" (Unix.gettimeofday ()) msg);
  flush _LOG

(*
 * PRIMITIVES
 *)

type chan = Unix.file_descr

let chan_of_tchan (Specif.Coq_existT(_, Datatypes.Coq_pair(c, _))) = c

let tchan_eq tc1 tc2 =
  chan_of_tchan tc1 = chan_of_tchan tc2

type fdesc = Unix.file_descr

let exec t prog st _ =
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
      log (Printf.sprintf "exec : %s -> (p: %d, c: %d)"
            prog (int_of_fd p) (int_of_fd c));
      Specif.Coq_existT(t, Datatypes.Coq_pair(p, st))
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
      log (Printf.sprintf "call : %s %s -> (r: %d, w: %d)"
            prog arg (int_of_fd r) (int_of_fd w));
      r (* TODO who closes r ? *)
  end

let select chans _ =
  let fds =
    List.map chan_of_tchan chans in
  let r, _, _ =
    Unix.handle_unix_error (fun _ ->
      Unix.select fds [] [] (-1.0)) () in
  let fd = List.hd r in
  log (Printf.sprintf "select : %s -> %d"
        (String.concat " " (List.map string_of_fd fds))
        (int_of_fd fd));
  List.find (fun (Specif.Coq_existT(_, Datatypes.Coq_pair(c, _))) -> c = fd) chans

let recv c n _ =
  let fd = chan_of_tchan c in
  let n = int_of_num n in
  let s = String.make n (Char.chr 0) in
  let r = 
    Unix.handle_unix_error (fun _ ->
      Unix.recv fd s 0 n []) ()
  in
  if r <> n then
    failwith "recv - wrong # of bytes"
  else begin
    log (Printf.sprintf "recv : %d %d -> \"%s\""
          (int_of_fd fd) n (String.escaped s));
    MlCoq.str_of_string s
  end

let send c s _ =
  let fd = chan_of_tchan c in
  let s = MlCoq.string_of_str s in
  let n = String.length s in
  let w =
    Unix.handle_unix_error (fun _ ->
      Unix.send fd s 0 n []) ()
  in
  if w <> n then
    failwith "send - wrong # of bytes"
  else begin
    log (Printf.sprintf "send : %d \"%s\" -> ()"
          (int_of_fd fd) (String.escaped s));
    ()
  end

external recv_fd_native : chan -> fdesc = "recv_fd_native"
let recv_fd (Specif.Coq_existT(_, Datatypes.Coq_pair(c, _))) _ =
  let fd = recv_fd_native c in
  log (Printf.sprintf "recv_fd : %d -> %d"
        (int_of_fd c) (int_of_fd fd));
  fd

external send_fd_native : chan -> fdesc -> unit = "send_fd_native"
let send_fd (Specif.Coq_existT(_, Datatypes.Coq_pair(c, _))) fd _ =
  send_fd_native c fd;
  log (Printf.sprintf "send_fd : %d %d -> ()"
        (int_of_fd c) (int_of_fd fd));
  ()
