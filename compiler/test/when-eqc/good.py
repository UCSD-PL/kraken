#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send('M', 'Good')
    time.sleep(3)

main()
