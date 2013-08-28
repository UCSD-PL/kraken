#!/usr/bin/python2.7

import gobject
import gtk
import Queue
import signal
import thread
import threading
import webkit


def asynchronous_gtk_message(fun):

  def worker((function, args, kwargs)):
    apply(function, args, kwargs)

  def fun2(*args, **kwargs):
    gobject.idle_add(worker, (fun, args, kwargs))

  return fun2


def synchronous_gtk_message(fun):

  def worker((R, condition, function, args, kwargs)):
    R.result = apply(function, args, kwargs)
    condition.acquire()
    condition.notify()
    condition.release()

  def fun2(*args, **kwargs):
    condition = threading.Condition()
    condition.acquire()
    class R: pass
    gobject.idle_add(worker, (R, condition, fun, args, kwargs))
    condition.wait()
    condition.release()
    return R.result

  return fun2


def launch_browser(uri, echo=True):
  # WARNING: You should call this function ONLY inside of GTK
  #          (i.e. use synchronous_gtk_message)

  window = gtk.OffscreenWindow()
  box = gtk.VBox(homogeneous=False, spacing=0)
  browser = webkit.WebView()

  window.set_default_size(800, 600)
  # Optional (you'll read about this later in the tutorial):
  window.connect('destroy', Global.set_quit)

  window.add(box)
  box.pack_start(browser, expand=True, fill=True, padding=0)

  window.show_all()

  # Note: All message passing stuff appears between these curly braces:
  # {
  message_queue = Queue.Queue()

  def title_changed(widget, frame, title):
    if title != 'null': message_queue.put(title)

  browser.connect('title-changed', title_changed)

  def web_recv():
    if message_queue.empty():
      return None
    else:
      msg = message_queue.get()
      if echo: print '>>>', msg
      return msg

  def web_send(msg):
    if echo: print '<<<', msg
    asynchronous_gtk_message(browser.execute_script)(msg)
  # }

  browser.open(uri)

  return window, box, browser, web_recv, web_send


class Global(object):
  quit = False
  @classmethod
  def set_quit(cls, *args, **kwargs):
    cls.quit = True

def my_quit_wrapper(fun):
  signal.signal(signal.SIGINT, Global.set_quit)
  def fun2(*args, **kwargs):
    try:
      x = fun(*args, **kwargs)
    finally:
      asynchronous_gtk_message(gtk.main_quit)()
      Global.set_quit()
    return x
  return fun2


def start_gtk_thread():
  gtk.gdk.threads_init()
  thread.start_new_thread(gtk.main, ())

def kill_gtk_thread():
  asynchronous_gtk_message(gtk.main_quit)()
