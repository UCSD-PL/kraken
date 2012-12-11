#!/usr/bin/env python

import socket, os, os.path, sys, re, time
import struct, passfd, atexit

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
  path = os.path.join(os.environ['KROOT'], 'log', '%s-%d-log' % (PROG, FD))
  LOG  = open(path, 'w', 0) # unbuffered

# tear down at exit
atexit.register(lambda: KCHAN.close())
atexit.register(lambda: LOG.close())

def log(msg):
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
1 : lambda : ['LoginReq', recv_str()],
2 : lambda : ['LoginRes', recv_num()],
3 : lambda : ['PubkeyReq', ],
4 : lambda : ['PubkeyRes', recv_str()],
5 : lambda : ['KeysignReq', recv_str()],
6 : lambda : ['KeysignRes', recv_str()],
7 : lambda : ['CreatePtyerReq', ],
8 : lambda : ['CreatePtyerRes', recv_fd(), recv_fd()],
9 : lambda : ['SysLoginReq', recv_str()],
10 : lambda : ['SysLoginRes', recv_str(), recv_num()],
11 : lambda : ['SysPubkeyReq', ],
12 : lambda : ['SysPubkeyRes', recv_str()],
13 : lambda : ['SysKeysignReq', recv_str()],
14 : lambda : ['SysKeysignRes', recv_str()],
15 : lambda : ['SysCreatePtyerReq', recv_str()],
16 : lambda : ['SysCreatePtyerRes', recv_fd(), recv_fd()],
  }[tag]()
  log('recv : %s' % msg_str(m))
  return m

def send(*m):
  tag = m[0]
  {
'LoginReq' : lambda : [send_num(1), send_str(m[1])],
'LoginRes' : lambda : [send_num(2), send_num(m[1])],
'PubkeyReq' : lambda : [send_num(3), ],
'PubkeyRes' : lambda : [send_num(4), send_str(m[1])],
'KeysignReq' : lambda : [send_num(5), send_str(m[1])],
'KeysignRes' : lambda : [send_num(6), send_str(m[1])],
'CreatePtyerReq' : lambda : [send_num(7), ],
'CreatePtyerRes' : lambda : [send_num(8), send_fd(m[1]), send_fd(m[2])],
'SysLoginReq' : lambda : [send_num(9), send_str(m[1])],
'SysLoginRes' : lambda : [send_num(10), send_str(m[1]), send_num(m[2])],
'SysPubkeyReq' : lambda : [send_num(11), ],
'SysPubkeyRes' : lambda : [send_num(12), send_str(m[1])],
'SysKeysignReq' : lambda : [send_num(13), send_str(m[1])],
'SysKeysignRes' : lambda : [send_num(14), send_str(m[1])],
'SysCreatePtyerReq' : lambda : [send_num(15), send_str(m[1])],
'SysCreatePtyerRes' : lambda : [send_num(16), send_fd(m[1]), send_fd(m[2])],
  }[tag]()
  log('send : %s' % msg_str(m))