#!/usr/bin/env python2.7

import msg, readline, time

def main():
  msg.init()
  try:
    while True:
      uin = raw_input("\n")
      if uin == ':new':
        msg.send(msg.NewTab)
      else:
        msg.send(msg.KeyPress, uin)
  except EOFError:
    pass
    #msg.send('Quit')

main()
