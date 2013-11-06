#!/usr/bin/env python2.7

import msg, time

def debug(s):
  print(" C: " + s)

def main():
  msg.init()
  debug("Spawned")
  i = 2
  while True:
    for f in {'doesnnotexist.txt', 'private.txt', 'public.txt'}:
      debug("Requesting " + f)
      msg.send(msg.FileReq, '../test/webserver/' + f)
      m = msg.recv()
      if m[0] == msg.FileRes:
        [_, _, fd] = m
        debug("access to file " + f + " was authorized, with content\n" + fd.read())
      elif m[0] == msg.FileResF:
        debug("access to file " + f + " was refused")
      else:
        debug("unexpected message " + str(m))
      time.sleep(i)
    i *= 2

main()

