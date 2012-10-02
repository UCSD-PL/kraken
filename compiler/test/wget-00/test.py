#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send('Wget', 'http://www.google.com')
    m = msg.recv()
    print(m)
    print(m[2].read())
    m[2].close()
    time.sleep(1)

main()
