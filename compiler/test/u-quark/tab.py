#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  while True:
    userinput = msg.recv()
    msg.send('Wget', userinput[1])
    html = msg.recv()
    msg.send('Display', html[2])

main()
