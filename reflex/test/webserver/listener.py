#!/usr/bin/env python2.7

import msg, time

def debug(s):
  print(" L: " + s)

def main():
  msg.init()
  debug("Spawned")
  i = 2
  while True:
    # A wrong request
    msg.send(msg.LoginReq, 'foo', 'baz', str(i))
    time.sleep(i)
    # A proper request
    msg.send(msg.LoginReq, 'foo', 'bar', str(i))
    time.sleep(i)
    i *= 2

main()

