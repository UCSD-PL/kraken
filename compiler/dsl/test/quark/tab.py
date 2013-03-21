#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    userinput = msg.recv()
    msg.send('Display', userinput[1])

main()
