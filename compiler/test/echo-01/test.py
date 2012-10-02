#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send('M1', 42)
    m = msg.recv()
    print(m)
    time.sleep(1)
    msg.send('M2', 'Hello world!')
    m = msg.recv()
    print(m)
    time.sleep(1)

main()
