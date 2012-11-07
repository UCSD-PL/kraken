#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send('M', 'Bad')
    time.sleep(3)

main()
