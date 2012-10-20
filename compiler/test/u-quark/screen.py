#!/usr/bin/env python2.7

import msg, webkitlib as WK

def main():
  WK.start_gtk_thread()
  browser, web_recv, web_send = (
    WK.synchronous_gtk_message(WK.launch_browser)('http://www.google.com'))
  msg.init()
  while True:
    m = msg.recv()
    browser.open(m[1])

main()
