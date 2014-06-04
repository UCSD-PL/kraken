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
      msg.send(msg.FileReq, f)
      m = msg.recv()
      if m[0] == msg.FileRes:
        [_, name, fd] = m
        contents = fd.read()
        debug("access to file " + name + " was authorized, with content\n" + contents)
        wfile.write(contents)
      elif m[0] == msg.FileResF:
        debug("access to file " + m[1] + " was refused")
      elif m[0] == msg.InitClient:
        rfile = m[1]
        wfile = m[2]
        print rfile, wfile
      else:
        debug("unexpected message " + str(m))
      time.sleep(i)
    i *= 2

main()

