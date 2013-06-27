#!/usr/bin/env python2.7

import msg, readline, time

def main():
  msg.init()
  try:
    while True:
      url = raw_input("\n")
      print url
      msg.send(msg.KeyPress, url)
  except EOFError:
    pass
    #msg.send('Quit')

main()
