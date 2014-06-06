#!/usr/bin/env python2.7

import msg, select, signal, time
from BaseHTTPServer import BaseHTTPRequestHandler

def debug(s):
  print(" C: " + s)

def handler(rfile, wfile):
  rfile.close()
  wfile.close()

def mkhandler(rfile, wfile):
  return lambda signal, frame: handler(rfile, wfile)

class HTTPRequest(BaseHTTPRequestHandler):
  def __init__(self, rfile, reqtxt):
    self.rfile = rfile
    self.raw_requestline = reqtxt #self.rfile.readline()
    print('REQ:[' + self.raw_requestline + ']')
    self.error_code = self.error_message = None
    self.parse_request()

def main():
  msg.init()
  debug("Spawned")

  m = msg.recv()
  if m[0] == msg.InitClient:
    rfile = m[1]
    wfile = m[2]
  else:
    debug("should have received InitClient message first")

  signal.signal(signal.SIGTERM, mkhandler(rfile, wfile))

  rdy = []
  while rdy == []:
    rdy, _, _ = select.select([rfile], [], [])
  data = rfile.readline()
  if data:
    req = HTTPRequest(rfile, data)
    if hasattr(req, 'path'):
      print('Resource: ' + req.path)
      msg.send(msg.FileReq, req.path)
      m = msg.recv()
      if m[0] == msg.FileRes:
        [_, name, fd] = m
        response = fd.read()
        contents = (
          "HTTP/1.0 200 OK\r\n"
          + "Content-Length: " + str(len(response)) + "\r\n"
          + "Content-Type: text/html\r\n\r\n"
          + response
        )
        debug("access to file " + name + " was authorized")
        wfile.write(contents)
      elif m[0] == msg.FileResF:
        debug("access to file " + m[1] + " was refused")
        response = "Access Forbidden"
        wfile.write(
          "HTTP/1.0 403 Forbidden\r\n"
          + "Content-Length: " + str(len(response)) + "\r\n"
          + "Content-Type: text/html\r\n\r\n"
          + response
        )
      else:
        debug("unexpected message " + str(m))

  debug('Shutting down')
  rfile.close()
  wfile.close()

  # YOU MUSTN'T DIE SOLDIER!
  while True:
    time.sleep(3600)

main()
