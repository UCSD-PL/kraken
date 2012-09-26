#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send_msg('Wget', 'http://www.google.com')
    m = msg.recv_msg()
    print(m)
    print(m[2].read())
    m[2].close()
    time.sleep(1)

main()
