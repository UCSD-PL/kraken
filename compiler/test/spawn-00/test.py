#!/usr/bin/env python2.7

import msg, os, time

def main():
  msg.init()
  msg.send_msg('M', 'Hello world!')
  m = msg.recv_msg()
  print('%d : %s' % (os.getpid(), str(m)))
  time.sleep(1)

main()
