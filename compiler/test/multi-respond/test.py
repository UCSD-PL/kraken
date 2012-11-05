#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send('M', '255', 'z')
    m = msg.recv()
    print(m)
    m = msg.recv()
    print(m)
    m = msg.recv()
    print(m)
    time.sleep(1)

main()
