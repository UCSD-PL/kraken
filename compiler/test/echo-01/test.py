#!/usr/bin/env python

import msg, time

def main():
  msg.init()
  while True:
    msg.send_msg('M1', 'Hello world!')
    m = msg.recv_msg()
    print(m)
    time.sleep(1)
    msg.send_msg('M2', 42)
    m = msg.recv_msg()
    print(m)
    time.sleep(1)

main()
