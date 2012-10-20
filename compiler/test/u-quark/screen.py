#!/usr/bin/env python2.7

import msg, time, subprocess

def main():
  msg.init()
  while True:
    m = msg.recv()
    p = subprocess.Popen(["lynx", "--dump", "--stdin"], stdin=subprocess.PIPE)
    (stdout, stderr) = p.communicate(input=m[1].read())
    print(stdout)

main()
