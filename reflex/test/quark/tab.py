#!/usr/bin/env python2.7

import msg, time
import webkitlib as WK
import sharedmem
import gobject
import webkit
import gtk
import time
import os
import tempfile

class Tab:
  browser = None
  shm_obj = None

  def req_resource(self, uri):
    print "Requesting:", uri
    msg.send(msg.ReqResource, uri)

  def handle_msgs(self, source, condition):
    m = msg.recv()
    if m[0] == msg.ResResource:
      print "Resource Response"
      tf = tempfile.NamedTemporaryFile(delete=False)
      tf.write(m[1].read())
      tf_name = tf.name
      tf.close()

      self.browser.open('file://' + tf_name)
    elif m[0] == msg.Go:
      print "Go"
      self.req_resource(m[1])
    elif m[0] == msg.MouseClick:
      if m[3] == 1:
        e_type = gtk.gdk.BUTTON_PRESS
        e_str = 'button-press-event'
      else:
        e_type = gtk.gdk.BUTTON_RELEASE
        e_str = 'button-release-event'

      e = gtk.gdk.Event(e_type)
      e.button = 1
      e.x = float(m[1])
      e.y = float(m[2])
      e.window = self.browser.get_window()
      self.browser.emit(e_str, e)
    elif m[0] == msg.KeyPress:
      e = gtk.gdk.Event(gtk.gdk.KEY_PRESS)
      e.window = self.browser.get_window()
      
      if int(m[1]) == 19:
        e.keyval = int(keysyms.Page_Up)
        e.hardware_keycode = gtk.gdk.keymap_get_default().get_entries_for_keyval(int(keysyms.Page_Up))[0][0]
      elif int(m[1]) == 20:
        e.keyval = int(keysyms.Page_Down)
        e.hardware_keycode = gtk.gdk.keymap_get_default().get_entries_for_keyval(int(keysyms.Page_Down))[0][0]
      elif int(m[1]) == 8:
        e.keyval = int(keysyms.BackSpace)
        e.hardware_keycode = gtk.gdk.keymap_get_default().get_entries_for_keyval(int(keysyms.BackSpace))[0][0]
      elif int(m[1]) == 9:
        e.keyval = int(keysyms.Tab)
        e.hardware_keycode = gtk.gdk.keymap_get_default().get_entries_for_keyval(int(keysyms.Tab))[0][0]
      elif int(m[1]) == 10:
        e.keyval = int(keysyms.Return)
        e.hardware_keycode = gtk.gdk.keymap_get_default().get_entries_for_keyval(int(keysyms.Return))[0][0]
      else :
        e.keyval = int(m[1])
        
      self.browser.emit('key-press-event', e)
        
    return True

  def render(self, x, y, width, height):
    self.shm_obj.write_webkit_as_png(x, y, width, height, self.browser)
    msg.send(msg.Display, str(self.shm_obj.get_shmid()))

  def expose(self, widget, event):
    area = event.area
    self.render(area.x, area.y, area.width, area.height)

  def report(self, widget, event):
    print dir(event)

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
    self.browser.add_events(gtk.gdk.KEY_PRESS_MASK | gtk.gdk.BUTTON_PRESS_MASK)
    win = gtk.OffscreenWindow()
    win.set_default_size(1100,700)
    win.add(self.browser)
    win.show_all()

    gtk.main()
    
tab = Tab()
tab.main()
