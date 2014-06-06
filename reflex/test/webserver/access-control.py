#!/usr/bin/env python2.7

import msg

credentials = {
  'foo' : 'bar',
  'default' : ' ',
}

owners = {
  '/index.html'  : {'foo', 'default'},
  'private.txt' : {},
}

def try_except(success, failure, *exceptions):
  try:
    return success()
  except exceptions or Exception:
    return failure() if callable(failure) else failure

def debug(s):
  print("AC: " + s)

def main():
  msg.init()
  debug("Spawned")
  while True:
    m = msg.recv()
    s = str(m)
    try:
      if m[0] == msg.ACLoginReq:
        [_, user, password, compid, rfile, wfile] = m
        try: ok = password == credentials[user]
        except KeyError: ok = False
        if ok:
          debug(user + " logged in")
          debug("RFile: " + str(rfile))
          debug("WFile: " + str(wfile))
          msg.send(msg.ACLoginResT, user, compid, rfile, wfile)
        else:
          debug(user + " refused (wrong password)")
          msg.send(msg.ACLoginResF, user, compid)
      elif m[0] == msg.ACFileReq:
        [_, user, compid, request] = m
        try: ok = user in owners[request]
        except KeyError: ok = False
        if ok:
          debug(user + " access to " + request + " authorized")
          msg.send(msg.ACFileResT, user, compid, request)
        else:
          debug(user + " access to " + request + " refused")
          msg.send(msg.ACFileResF, user, compid, request)
      else:
        debug("Unhandled message " + s)
    except ValueError:
      debug("Unexpected payload " + s)

main()

