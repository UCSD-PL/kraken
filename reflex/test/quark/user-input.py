#!/usr/bin/env python2.7

import msg, readline, time

def main():
  msg.init()
  try:
    while True:
      url = raw_input("\n")
      msg.send('Input', url)
  except EOFError:
    msg.send('Quit')

main()
