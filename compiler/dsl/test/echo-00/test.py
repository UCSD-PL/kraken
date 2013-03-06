#!/usr/bin/env python2.7

import msg, time

def main():
  print("main")
  msg.init()
  while True:
    print("send")
    msg.send('M', 'Hello world!')
    print("recv")
    m = msg.recv()
    print(m)
    time.sleep(1)

main()
