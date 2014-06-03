(* conversion between Coq and ML values *)
(* NOTE ascii has least significant bit first *)

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
    ( c land   1 <> 0
    , c land   2 <> 0
    , c land   4 <> 0
    , c land   8 <> 0
    , c land  16 <> 0
    , c land  32 <> 0
    , c land  64 <> 0
    , c land 128 <> 0
    )

let int_of_num = function ReflexBase.Num (l, h) ->
  let l = Char.code (char_of_ascii l) in
  let h = Char.code (char_of_ascii h) in
  l + h * 256

let num_of_int i =
  let l = ascii_of_char (Char.chr (i mod 256)) in
  let h = ascii_of_char (Char.chr (i / 256)) in
  ReflexBase.Num (l, h)

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

let string_of_str s =
  implode (List.map char_of_ascii s)

let str_of_string s =
  List.map ascii_of_char (explode s)

(* Forked components need to know which file descriptor to use for
 * communicating with the kernel.
 *
 * Unfortunately, Unix.file_descr is declared as an abstract type in the
 * Unix module signature, which hides its implementation and thus prevents
 * sending some representation of a file descriptor to a forked component.
 *
 * These functions expose the implementation of Unix.file_descr as an int,
 * which in turn enables passing a representation of a file descriptor to
 * forked components.
 *)
let int_of_fd : Unix.file_descr -> int =
  Obj.magic

let fd_of_int : int -> Unix.file_descr =
  Obj.magic

let fd_of_cfd cfd =
  fd_of_int (int_of_num cfd)

let cfd_of_fd fd =
  num_of_int (int_of_fd fd)

let string_of_fd fd =
  string_of_int (int_of_fd fd)

(* logging *)

let _LOG =
  let mode = Unix.O_CREAT :: Unix.O_WRONLY :: [] in
  let perm = 0o644 in
  (* find fresh name *)
  let rec loop i =
    let nm = Printf.sprintf ".reflex-log-%03d" i in
    if Sys.file_exists nm then
      loop (i + 1)
    else
      Unix.openfile nm mode perm
  in
  loop 0

let log msg =
  let entry =
    Printf.sprintf "%15s @ %f || %s\n"
      "K" (Unix.gettimeofday ()) msg in
  ignore (Unix.write _LOG entry 0 (String.length entry))

(* primitives *)

let run prog fd args =
  let v = prog :: string_of_fd fd :: string_of_fd _LOG :: args in
  Unix.handle_unix_error (fun _ ->
    Unix.execv prog (Array.of_list v)) ()

let exec cprog cargs _ =
  let prog = string_of_str cprog in
  let args = List.map string_of_str cargs in
  let p, c = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  match Unix.fork () with
  | 0 -> (* child *) begin
    Unix.close p;
    run prog c args
  end
  | cpid -> (* parent *) begin
    Unix.close c;
    log (Printf.sprintf "exec : %s %s -> (p: %d, c: %d)"
          prog (String.concat " " args) (int_of_fd p) (int_of_fd c));
    cfd_of_fd p
  end

let call cprog cargs _ =
  let prog = string_of_str cprog in
  log (Printf.sprintf "call : %s " prog);
  let args = List.map string_of_str cargs in
  (* let r, w = Unix.pipe () in *)
  let r, w = Unix.socketpair Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  match Unix.fork () with
  | 0 -> (* child *) begin
    Unix.close r;
    run prog w args
  end
  | cpid -> (* parent *) begin
    Unix.close w;
    log (Printf.sprintf "call : %s %s -> (r: %d, w: %d)"
          prog (String.concat " " args) (int_of_fd r) (int_of_fd w));
    (* TODO who closes r ? *)
    cfd_of_fd r
  end

let select cfds _ =
  let fds = List.map fd_of_cfd cfds in
  let r, _, _ =
    Unix.handle_unix_error (fun _ ->
      Unix.select fds [] [] (-1.0)) () in
  let fd = List.hd r in
  log (Printf.sprintf "select : %s -> %d"
        (String.concat " " (List.map string_of_fd fds)) (int_of_fd fd));
  let cfd =
    List.find
      (fun cfd -> fd_of_cfd cfd = fd)
      cfds
  in
  Specif.Coq_existT (cfd, Obj.magic ())

let recv cfd n _ =
  let fd = fd_of_cfd cfd in
  let i = int_of_num n in
  let s = String.make i (Char.chr 0) in
  let r =
    Unix.handle_unix_error (fun _ ->
      Unix.recv fd s 0 i []) ()
  in
  if r <> i then
    failwith (Printf.sprintf "recv - wrong # of bytes from %d (%d <> %d):(%s)" (int_of_fd fd) r i s)
  else begin
    log (Printf.sprintf "recv : %d %d -> \"%s\""
          (int_of_fd fd) i (String.escaped s));
    str_of_string s
  end

let send cfd s _ =
  let fd = fd_of_cfd cfd in
  let s = string_of_str s in
  let i = String.length s in
  let w =
    Unix.handle_unix_error (fun _ ->
      Unix.send fd s 0 i []) ()
  in
  if w <> i then
    failwith "send - wrong # of bytes"
  else begin
    log (Printf.sprintf "send : %d \"%s\" -> ()"
          (int_of_fd fd) (String.escaped s));
    ()
  end

let oracle _ =
  Obj.magic ()

external recv_fd_native : Unix.file_descr -> Unix.file_descr =
  "recv_fd_native"

let recv_fd cfd _ =
  let fd = fd_of_cfd cfd in
  let x = recv_fd_native fd in
  log (Printf.sprintf "recv_fd : %d -> %d"
        (int_of_fd fd) (int_of_fd x));
  cfd_of_fd x

external send_fd_native : Unix.file_descr -> Unix.file_descr -> unit =
  "send_fd_native"

let send_fd cfd x _ =
  let fd = fd_of_cfd cfd in
  let x = fd_of_cfd x in
  send_fd_native fd x;
  log (Printf.sprintf "send_fd : %d %d -> ()"
        (int_of_fd fd) (int_of_fd x));
  ()

(* BEGIN:UserPrimitives *)
let _INVOKE_FD_MAP : (string * (string list -> Unix.file_descr)) list =
  []

let _INVOKE_STR_MAP : (string * (string list -> string)) list =
  []
(* END:UserPrimitives *)

let invoke_fd cprog cargs _ =
  let prog = string_of_str cprog in
  let args = List.map string_of_str cargs in
  let fd = (List.assoc prog _INVOKE_FD_MAP) args in
  log (Printf.sprintf "invoke_fd : %s [%s] -> %d"
    prog (String.concat ", " args) (int_of_fd fd));
  cfd_of_fd fd

let invoke_str cprog cargs _ =
  let prog = string_of_str cprog in
  let args = List.map string_of_str cargs in
  let s = (List.assoc prog _INVOKE_STR_MAP) args in
  log (Printf.sprintf "invoke_str : %s [%s] -> %s"
    prog (String.concat ", " args) s);
  str_of_string s
