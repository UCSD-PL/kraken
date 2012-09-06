#!/usr/bin/env python

import sys, socket, struct

def recvNum(c):
  s = c.recv(1)
  n = struct.unpack('>B', s)[0]
  print '<< %d' % n
  return n

def recvStr(c):
  n = recvNum(c)
  s = c.recv(n)
  print '<< "%s"' % s
  return s

def sendNum(c, n):
  s = struct.pack('>B', n)
  c.send(s)
  print '>> %d' % n

def sendStr(c, s):
  sendNum(c, len(s))
  c.send(s)
  print '>> "%s"' % s

def main():
  f = int(sys.argv[1])
  c = socket.fromfd(f, socket.AF_UNIX, socket.SOCK_STREAM)
  sendNum(c, 1)
  sendStr(c, 'hello world')
  n = recvNum(c)
  x = recvStr(c)

main()
