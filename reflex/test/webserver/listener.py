#!/usr/bin/env python2.7

import msg, socket, time
import uuid

HOST_NAME = 'localhost' # !!!REMEMBER TO CHANGE THIS!!!
PORT_NUMBER = 9000 # Maybe set this to 9000.

def debug(s):
  print(" L: " + s)

if __name__ == '__main__':
  msg.init()
  debug("Spawned")
  s = socket.socket()
  try:
    s.bind((HOST_NAME, PORT_NUMBER))
    print time.asctime(), "Server Starts - %s:%s" % (HOST_NAME, PORT_NUMBER)
    while True:
      s.listen(0)
      (bs, addr) = s.accept()
      debug('Accepting: ' + str(addr))
      msg.send(msg.LoginReq, 'default', ' ', str(uuid.uuid4()), bs, bs)
  except:
    s.close()
    print time.asctime(), "Server Stops - %s:%s" % (HOST_NAME, PORT_NUMBER)
