#!/usr/bin/env python2.7

import msg

def main():
  msg.init ()
  while True:
    m = msg.recv()
    print(m)

main()
