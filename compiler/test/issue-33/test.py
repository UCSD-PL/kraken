#!/usr/bin/env python2.7

import msg

def main():
  msg.init()
  m = msg.recv()
  print(m)
  while True:
    pass

main()
