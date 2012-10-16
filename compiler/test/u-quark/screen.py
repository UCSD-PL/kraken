#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  msg.send('Dummy', 'dummy')
  while True:
    m = msg.recv()
    html = urllib2.urlopen(m[2].read()).read()
    msg.send('HTML', html)

main()
