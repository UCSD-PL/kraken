#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send('ReqN')
    m = msg.recv()
    print(m)
    time.sleep(1)

main()
