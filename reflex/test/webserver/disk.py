#!/usr/bin/env python2.7

import msg, os, socket

def debug(s):
  print(" D: " + s)

def main():
  msg.init()
  debug("Spawned")
  while True:
    m = msg.recv()
    if m[0] == msg.DFileReq:
      [_, user, compid, request] = m
      fd = open("/home/ucsd/kraken/reflex/test/webserver/" + request)
      msg.send(msg.DFileRes, user, compid, request, fd)
    else:
      debug("Unhandled message " + str(m))
    debug(str(m))

main()

