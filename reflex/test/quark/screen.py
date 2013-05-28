#!/usr/bin/env python2.7

import msg, webkitlib as WK

def handle(browser):
  def go():
    m = msg.recv()
    { 'Display' : lambda: browser.open(m[1])
    , 'Quit'    : lambda: sys.exit(0)
    }.get(m[0], go)()
  go()

def main():
  WK.start_gtk_thread()
  browser, web_recv, web_send = (
    WK.synchronous_gtk_message(WK.launch_browser)('http://www.google.com'))
  msg.init()
  while True:
    handle(browser)

main()
