#!/usr/bin/env python2.7

import msg, time
import webkitlib as WK
import sharedmem
import gobject
import webkit
import gtk
import time

class Tab:
  browser = None
  shm_obj = None

  def handle_msgs(self, source, condition):
    m = msg.recv()
    if m[0] == msg.KeyPress:
      # Should be a url (for now)
      # send to webkit, somehow
      self.browser.open(m[1])
    elif m[0] == msg.Go:
      self.browser.open(m[1])
    return True

  def render(self, x, y, width, height):
    self.shm_obj.write_webkit_as_png(x, y, width, height, self.browser)
    msg.send(msg.Display, str(self.shm_obj.get_shmid()))

  def expose(self, widget, event):
    area = event.area
    self.render(area.x, area.y, area.width, area.height)

  def main(self):
    self.shm_obj = sharedmem.Shm()
    self.shm_obj.init()
    msg.init()
    gobject.io_add_watch(msg.KCHAN.fileno(), gobject.IO_IN, self.handle_msgs)

    #WK.start_gtk_thread()
    #win, box, self.browser, web_recv, web_send = (
    #  WK.synchronous_gtk_message(WK.launch_browser)('http://www.google.com'))

    self.browser = webkit.WebView()
    self.browser.connect_after('expose-event', self.expose)
    win = gtk.OffscreenWindow()
    win.set_default_size(1100,700)
    win.add(self.browser)
    win.show_all()

    gtk.main()
    
tab = Tab()
tab.main()
