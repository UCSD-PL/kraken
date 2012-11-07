#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    print(msg.recv())

main()
