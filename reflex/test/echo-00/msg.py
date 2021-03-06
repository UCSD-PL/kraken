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
#V  path = os.path.join(os.environ['KROOT'], 'log', '%s-%d-log' % (PROG, FD))
#V  LOG  = open(path, 'w', 0) # unbuffered

# tear down at exit
atexit.register(lambda: KCHAN.close())
atexit.register(lambda: LOG.close())

def log(msg):
  return
  # FD - 1 should be the kernel's pipe for this component
#V  LOG.write('%15s @ %f || %s\n' %
#V      ('%s(%d)' % (PROG, FD - 1), time.time(), msg))

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
0 : lambda : ['M', recv_str()],
  }[tag]()
  log('recv : %s' % msg_str(m))
  return m

def send(*m):
  tag = m[0]
  {
'M' : lambda : [send_num(0), send_str(m[1])],
  }[tag]()
  log('send : %s' % msg_str(m))
