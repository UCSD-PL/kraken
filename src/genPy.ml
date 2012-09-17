open Common
open Spec

let py_recv_typ = function
  | Num -> "recv_num"
  | Str -> "recv_str"
  | Fdesc -> "recv_fd"

let py_send_typ = function
  | Num -> "send_num"
  | Str -> "send_str"
  | Fdesc -> "send_fd"

let py_recv_msg tag_map m =
  let args =
    m.payload
      |> List.map py_recv_typ
      |> String.concat ", "
  in
  mkstr "%d : lambda _ : ['%s', %s],"
    (List.assoc m.tag tag_map) m.tag args

let py_send_msg tag_map m =
  let args =
    m.payload
      |> List.mapi (fun i t -> mkstr "%s(m[%d])" (py_send_typ t) (i + 1))
      |> String.concat ", "
  in
  mkstr "'%s' : lambda _ : [send_num(%d), %s],"
    m.tag (List.assoc m.tag tag_map) args

(* py lib template has string holes for
 *  1. recv_msg cases
 *  2. send_msg cases
 *)
let py_template = format_of_string "
import socket, struct, sys

KCHAN = None

def init():
  global KCHAN
  fd = int(sys.argv[1])
  KCHAN = socket.fromfd(fd, socket.AF_UNIX, socket.SOCK_STREAM)

def recvNum():
  s = KCHAN.recv(1)
  n = struct.unpack('>B', s)[0]
  return n

def recvStr():
  n = recvNum()
  s = KCHAN.recv(n)
  return s

def sendNum(n):
  s = struct.pack('>B', n)
  KCHAN.send(s)

def sendStr(s):
  sendNum(len(s))
  KCHAN.send(s)

def recvMsg():
  tag = recvNum()
  return {
%s
  }[tag](0)

def sendMsg(*m):
  tag = m[0]
  {
%s
  }[tag](0)
"

let py_lib s =
  let tm = gen_tag_map s in
  let fmt l f =
    String.concat "\n" (List.map f l)
  in
  mkstr py_template
    (fmt s.msg_decl (py_recv_msg tm))
    (fmt s.msg_decl (py_send_msg tm))

let py_test s =
  ""
