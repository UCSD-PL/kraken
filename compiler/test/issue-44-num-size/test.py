#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init ()
  while True:
    m = msg.recv()
    print(m)
    time.sleep(1)

main()
