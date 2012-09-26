#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send_msg('M1', 42)
    m = msg.recv_msg()
    print(m)
    time.sleep(1)
    msg.send_msg('M2', 'Hello world!')
    m = msg.recv_msg()
    print(m)
    time.sleep(1)

main()
