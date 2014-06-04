#!/usr/bin/env python2.7

import socket, os, os.path, sys, re, time
import struct, passfd, atexit

LoginReq     = "LoginReq"
ACLoginReq   = "ACLoginReq"
ClientExists = ""
ACLoginResT  = "ACLoginResT"
ACLoginResF  = "ACLoginResF"
LoginResT    = "LoginResT"
LoginResF    = "LoginResF"
FileReq      = "FileReq"
ACFileReq    = "ACFileReq"
ACFileResT   = "ACFileResT"
ACFileResF   = "ACFileResF"
DFileReq     = "DFileReq"
DFileRes     = "DFileRes"
FileRes      = "FileRes"
FileResF     = "FileResF"
InitClient   = "InitClient"

FD    = None
KCHAN = None
PROG  = None
LOG   = None

def init():
  global FD, KCHAN, PROG, LOG

  # set up communication with kernel
  FD = int(sys.argv[1])
  KCHAN = socket.fromfd(FD, socket.AF_UNIX, socket.SOCK_STREAM)

  # set up logging
  PROG = os.path.basename(sys.argv[0])
  path = os.path.join(os.environ['KRAKEN'], 'log', '%s-%d-log' % (PROG, FD))
  LOG  = open(path, 'w', 0) # unbuffered

  # tear down at exit
  atexit.register(lambda: KCHAN.close())
  atexit.register(lambda: LOG.close())

def log(msg):
  #LOG.write(msg)
  # FD - 1 should be the kernel's pipe for this component
  LOG.write('%15s @ %f || %s\n' %
     ('%s(%d)' % (PROG, FD - 1), time.time(), msg))

def recv_num():
  s = KCHAN.recv(2)
  n = struct.unpack('>H', s)[0]
  return n

def recv_str():
  n = recv_num()
  s = KCHAN.recv(n)
  return s

def recv_fd():
  fd, _ = passfd.recvfd(KCHAN)
  f = os.fdopen(fd, 'r')
  return f

def send_num(n):
  s = struct.pack('>H', n)
  KCHAN.send(s)

def send_str(s):
  send_num(len(s))
  KCHAN.send(s)

def send_fd(f):
  fd = f.fileno()
  passfd.sendfd(KCHAN, fd)

def msg_str(m):
  def param_str(p):
    if isinstance(p, int):
      return '%d' % p
    elif isinstance(p, str):
      p = re.escape(p)
      p = p.replace('\n', '\\n')
      return '"%s"' % p
    else:
      # assume fd
      return 'fd(%d)' % p.fileno()
  params = ", ".join(map(param_str, m[1:]))
  return '%s(%s)' % (m[0], params)

def recv():
  tag = recv_num()
  m = {
    0 : lambda : [LoginReq    , recv_str(), recv_str(), recv_str(), recv_fd(), recv_fd()],
    1 : lambda : [ACLoginReq  , recv_str(), recv_str(), recv_str(), recv_fd(), recv_fd()],
    2 : lambda : [ClientExists, recv_str(), recv_str()],
    3 : lambda : [ACLoginResT , recv_str(), recv_str(), recv_fd(), recv_fd()],
    4 : lambda : [ACLoginResF , recv_str(), recv_str()],
    5 : lambda : [LoginResT   , recv_str(), recv_str()],
    6 : lambda : [LoginResF   , recv_str(), recv_str()],
    7 : lambda : [FileReq     , recv_str()],
    8 : lambda : [ACFileReq   , recv_str(), recv_str(), recv_str()],
    9 : lambda : [ACFileResT  , recv_str(), recv_str(), recv_str()],
   10 : lambda : [ACFileResF  , recv_str(), recv_str(), recv_str()],
   11 : lambda : [DFileReq    , recv_str(), recv_str(), recv_str()],
   12 : lambda : [DFileRes    , recv_str(), recv_str(), recv_str(), recv_fd()],
   13 : lambda : [FileRes     , recv_str(), recv_fd()],
   14 : lambda : [FileResF    , recv_str()],
   15 : lambda : [InitClient  , recv_fd(), recv_fd()],
}[tag]()
  log('recv : %s' % msg_str(m))
  return m

def send(*m):
  tag = m[0]
  {
    LoginReq    : lambda : [send_num(0), send_str(m[1]), send_str(m[2]), send_str(m[3]), send_fd(m[4]), send_fd(m[5])],
    ACLoginReq  : lambda : [send_num(1), send_str(m[1]), send_str(m[2]), send_str(m[3]), send_fd(m[4]), send_fd(m[5])],
    ClientExists: lambda : [send_num(2), send_str(m[1]), send_str(m[2])],
    ACLoginResT : lambda : [send_num(3), send_str(m[1]), send_str(m[2]), send_fd(m[3]), send_fd(m[4])],
    ACLoginResF : lambda : [send_num(4), send_str(m[1]), send_str(m[2])],
    LoginResT   : lambda : [send_num(5), send_str(m[1]), send_str(m[2])],
    LoginResF   : lambda : [send_num(6), send_str(m[1]), send_str(m[2])],
    FileReq     : lambda : [send_num(7), send_str(m[1])],
    ACFileReq   : lambda : [send_num(8), send_str(m[1]), send_str(m[2]), send_str(m[3])],
    ACFileResT  : lambda : [send_num(9), send_str(m[1]), send_str(m[2]), send_str(m[3])],
    ACFileResF  : lambda : [send_num(10), send_str(m[1]), send_str(m[2]), send_str(m[3])],
    DFileReq    : lambda : [send_num(11), send_str(m[1]), send_str(m[2]), send_str(m[3])],
    DFileRes    : lambda : [send_num(12), send_str(m[1]), send_str(m[2]), send_str(m[3]), send_fd(m[4])],
    FileRes     : lambda : [send_num(13), send_str(m[1]), send_fd(m[2])],
    FileResF    : lambda : [send_num(14), send_str(m[1])],
    InitClient  : lambda : [send_num(15), send_fd(m[1]), send_fd(m[2])]
  }[tag]()
  log('send : %s' % msg_str(m))

