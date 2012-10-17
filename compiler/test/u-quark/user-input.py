#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    msg.send('Input', 'http://cs.ucsd.edu/~d1jang')
    time.sleep(3)
    msg.send('Input', 'http://cs.ucsd.edu/~vrobert')
    time.sleep(3)
    msg.send('Input', 'http://cs.ucsd.edu/~ztatlock')
    time.sleep(3)

main()
