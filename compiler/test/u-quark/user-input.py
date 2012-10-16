#!/usr/bin/env python2.7

import msg, time

def main():
  msg.init()
  msg.send('Go', 'http://www.google.com')
  google = msg.recv()
  print(m[2].read())
  # render m[2].read()
  time.sleep(3)
  msg.send('Tab', 'http://www.facebook.com')
  facebook = msg.recv()
  print(m[2].read())
  # render m[2].read()
  time.sleep(3)

main()
