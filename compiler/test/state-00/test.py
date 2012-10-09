#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send_msg('ReqCurTab')
    m = msg.recv_msg()
    print(m)
    time.sleep(1)

main()
