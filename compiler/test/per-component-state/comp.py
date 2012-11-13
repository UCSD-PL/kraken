#!/usr/bin/env python2.7

import msg, os, time

def main():
  msg.init()
  while True:
    msg.send('WhoAmI')
    m = msg.recv()
    print(str(m))
    time.sleep(3)

main()
