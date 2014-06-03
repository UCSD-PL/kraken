#!/usr/bin/python

import sys
import os
import tempfile
import gobject
import gtk 
import socket
import shm
import threading
import time
import struct
import cairo
import array
import cPickle as pickle

import message
import config

#gtk.gdk.threads_init()

def olog(str):
    olog_nonl(str + "\n")

def olog_nonl(str):
    sys.stderr.write("O: " + str)
    sys.stderr.flush()

class UI:
    shm_obj = None
    sem_obj = None
    cr = None
    pixbuf = None
    rectangle = None

    def redraw(self) :
        print "redraw-----"
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

                        # shm_obj = self.shm_obj
                        # size = struct.unpack_from("i", shm_obj.read(4,4*0))[0]
                        # x = struct.unpack_from("i", shm_obj.read(4,4*1))[0]
                        # y = struct.unpack_from("i", shm_obj.read(4,4*2))[0]
                        # width = struct.unpack_from("i", shm_obj.read(4,4*3))[0]
                        # height = struct.unpack_from("i", shm_obj.read(4,4*4))[0]
                        # pixels = pickle.loads(shm_obj.read(size,4*5))
                        # pixbuf = gtk.gdk.pixbuf_new_from_array(pixels, gtk.gdk.COLORSPACE_RGB,8)   
                    finally :
                        self.sem_obj.V()
                        pass

                    #print pixbuf.get_width()
                    #print pixbuf.get_height()
                    #print x
                    #print y
                    pixbuf.copy_area(0, 0, pixbuf.get_width(), pixbuf.get_height(), self.pixbuf, x, y)
                    self.rectangle = (x,y,width,height)
                    self.win.queue_draw_area(x,y, pixbuf.get_width(), pixbuf.get_height())

                except TypeError:
                    olog("unexpected error:" + str(sys.exc_info()[0]))
                    pass
                except :
                    olog("unexpected general error:" + str(sys.exc_info()[0]))
                    pass                    
            finally:
                self.thread_lock.release()
                pass
                
    def window_destroyed(self, widget, data=None):
        #olog("window is destroyed")
        gtk.main_quit()

    def expose(self, widget, event):
        # Load Cairo drawing context.
        self.thread_lock.acquire()
        try :
            if self.pixbuf <> None :
                area = event.area
                #olog("x,y,width,height = %d %d %d %d" % (area.x, area.y, area.width, area.height))
                self.pixbuf.render_to_drawable(self.win.window, gtk.gdk.GC(self.win.window), area.x, area.y, area.x, area.y, area.width, area.height)

                # if self.rectangle <> None:
                #     cr = widget.window.cairo_create()
                #     cr.set_line_width(1)
                #     cr.set_source_rgb(255, 0, 0)
                #     cr.rectangle(self.rectangle[0], self.rectangle[1], self.rectangle[2], self.rectangle[3])
                #     cr.stroke()
        finally:
            self.thread_lock.release()

    def handle_input(self, source, condition):
        #olog("handle_input:")
        m = self.message_handler.recv()
        if m[0] == message.RenderCompleted :
            # load a new shared memory
            #olog("display msg is received")
            shmid = int(m[1])
            if self.shm_obj <> None:
                if self.shm_obj.shmid == shmid :
                    self.redraw()
                else:
                    self.thread_lock.acquire()
                    try :
                        self.shm_obj.detach()
                        self.shm_obj = shm.memory(shmid)
                        self.sem_obj = shm.semaphore(shm.getsemid(shmid))
                        self.shm_obj.attach()
                    finally:
                        self.thread_lock.release()
            else :
                self.thread_lock.acquire()
                try :
                    self.shm_obj = shm.memory(shmid)
                    self.sem_obj = shm.semaphore(shm.getsemid(shmid))
                    self.shm_obj.attach()
                finally:
                    self.thread_lock.release()
        else :
            sys.stderr.write('invalid event type\n')
            sys.exit(1)
        gobject.io_add_watch(self.soc.fileno(), gobject.IO_IN, self.handle_input)
        return False

    def handle_hup(self, source, condition):
        gtk.main_quit()
        return False

    def main(self):
        self.thread_lock = threading.Lock()
        self.shm_obj = None
        self.sem_obj = None

        self.message_handler = message.MessageHandler()
        self.soc = self.message_handler.KCHAN
        # socket.fromfd(int(sys.argv[1]), msg.FAMILY, msg.TYPE)

        gobject.io_add_watch(self.soc.fileno(), gobject.IO_IN, self.handle_input)
        gobject.io_add_watch(self.soc.fileno(), gobject.IO_HUP, self.handle_hup)

        window = gtk.Window() #gtk.WINDOW_TOPLEVEL) 
        window.set_decorated(False)
        window.set_app_paintable(True)
        screen = window.get_screen()
        rgba = screen.get_rgba_colormap()
        window.set_colormap(rgba)

        window.set_title("Quark Web Browser Output")
        vsize = config.ydimension
        window.set_default_size(1100, vsize - 200)
        #window.set_keep_above(True)
        window.set_decorated(False)
        window.connect("destroy", self.window_destroyed)
        window.connect('expose-event', self.expose)
        #window.move(100,300)
        window.move(63,143)
        self.win = window

        window.show_all()

        (x,y,width,height,depth) = self.win.window.get_geometry()
        #width = 4000
        #height = 4000
        #self.pixbuf = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, False, 8, width, height)
        self.pixbuf = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, False, 8, width, height)
        gtk.main()

    def curr_tab(self):
        return self.tabs[self.curr]        

UI().main()
