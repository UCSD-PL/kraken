#!/usr/bin/env python2.7

import msg, webkitlib as WK
import gtk
import threading
import gobject
import shm
import sys
import struct

class UI:

  win = None
  pixbuf = None
  thread_lock = None
  rectangle = None
  sem_obj = None
  shm_obj = None

  def redraw(self) :
    if self.sem_obj != None:
      self.thread_lock.acquire()
      try :
        try :
          self.sem_obj.P()
          try :
            shm_obj = self.shm_obj
            size = struct.unpack_from("i", shm_obj.read(4,4*0))[0]
            x = struct.unpack_from("i", shm_obj.read(4,4*1))[0]
            y = struct.unpack_from("i", shm_obj.read(4,4*2))[0]
            width = struct.unpack_from("i", shm_obj.read(4,4*3))[0]
            height = struct.unpack_from("i", shm_obj.read(4,4*4))[0]
            pixbufloader = gtk.gdk.PixbufLoader()
            pixbufloader.write(shm_obj.read(size,4*5))
            pixbufloader.close()                
            pixbuf = pixbufloader.get_pixbuf()
            
          finally :
            self.sem_obj.V()
            pass
          
          pixbuf.copy_area(0, 0, pixbuf.get_width(), pixbuf.get_height(), self.pixbuf, x, y)
          self.rectangle = (x,y,width,height)
          self.win.queue_draw_area(x,y, pixbuf.get_width(), pixbuf.get_height())
          
        except TypeError:
          msg.log("unexpected error:" + str(sys.exc_info()[0]))
          pass
      except :
        msg.log("unexpected general error:" + str(sys.exc_info()))
        pass                    
      finally:
        self.thread_lock.release()
        pass

  def handle_display_shm(self, m):
    shm_id = int(m[1])
    if self.shm_obj <> None:
      if self.shm_obj.shmid == shm_id :
        pass #self.redraw()
      else:
        self.thread_lock.acquire()
        try :
          self.shm_obj.detach()
          self.shm_obj = shm.memory(shm_id)
          self.sem_obj = shm.semaphore(shm.getsemid(shm_id))
          self.shm_obj.attach()
        finally:
          self.thread_lock.release()
    else :
      self.thread_lock.acquire()
      try :
        self.shm_obj = shm.memory(shm_id)
        self.sem_obj = shm.semaphore(shm.getsemid(shm_id))
        self.shm_obj.attach()
      finally:
        self.thread_lock.release()
    self.redraw()

  def handle_msgs(self, source, condition):
    m = msg.recv()
    if m[0] == msg.Display:
      self.handle_display_shm(m)
    return True
  
  def window_destroyed(self, widget, data=None):
    gtk.main_quit()

  def expose(self, widget, event):
    self.thread_lock.acquire()
    try :
      if self.pixbuf <> None :
        area = event.area
        self.pixbuf.save('/home/daniel/pixbufaft.png', 'png')
        self.pixbuf.render_to_drawable(self.win.window, gtk.gdk.GC(self.win.window), area.x, area.y, area.x, area.y, area.width, area.height)
        
    finally:
      self.thread_lock.release()

  def main(self):
    self.thread_lock = threading.Lock()

    window = gtk.Window() #gtk.WINDOW_TOPLEVEL) 
    window.set_decorated(False)
    window.set_app_paintable(True)
    screen = window.get_screen()
    rgba = screen.get_rgba_colormap()
    window.set_colormap(rgba)
    
    window.set_title("Quark Web Browser Output")
    window.set_default_size(1100,710)
    window.set_decorated(False)
    window.connect("destroy", self.window_destroyed)
    window.connect('expose-event', self.expose)
    window.move(100,300)
    self.win = window
                
    window.show_all()

    (x,y,width,height,depth) = self.win.window.get_geometry()
    self.pixbuf = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, False, 8, width, height)

    msg.init()
    gobject.io_add_watch(msg.KCHAN.fileno(), gobject.IO_IN, self.handle_msgs)

    gtk.main()

ui = UI()
ui.main()
