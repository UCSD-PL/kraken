import shm
import random
import gtk
import sys
import msg
import struct

class Shm:

  sem_obj = None
  shm_obj = None
  shm_size = 0

  def get_shmid(self):
    return self.shm_obj.shmid

  # mostly copied from shm_wrapper.py
  def create_memory(self, size, permissions = 0600):
      """ Creates a new shared memory segment. One can destroy it either
      by calling the module-level method remove_memory() or by calling
      the .remove() method of a handle to said memory.
      """
      memory = None

      while not memory:
          key = random.randint(1, sys.maxint - 1)
          try:
              memory = shm.create_memory(key, size, permissions)
              # for output process
              #memory.setuid(quarkexec.quark_output_uid)
          except shm.error, ExtraData:
              msg.log("unexpected error:" + str(sys.exc_info()))
              if shm.memory_haskey(key):
                  pass
              else:
                  raise shm.error, ExtraData
      return memory

  def pixbuf_save_func(self, buf, data=None):
      self.shm_obj.write(buf, self.shm_size)
      self.shm_size = self.shm_size + len(buf)
      return True

  # real rendering process
  def write_webkit_as_png(self, x, y, width, height, view):
      win = view.get_window()
      pixbuf = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB,False,8,width,height)
      pixbuf.get_from_drawable(win,view.get_colormap(),x,y,0,0,width,height)
      self.shm_size = 4 * 5 # shm_size, x, y, width, height

      self.sem_obj.P()
    
      try :
          pixbuf.save_to_callback(self.pixbuf_save_func, 'png')
          self.shm_obj.write(struct.pack("i", self.shm_size-4*5), 4*0)
          self.shm_obj.write(struct.pack("i", x), 4*1)
          self.shm_obj.write(struct.pack("i", y), 4*2)
          self.shm_obj.write(struct.pack("i", width), 4*3)
          self.shm_obj.write(struct.pack("i", height), 4*4)

      finally :
          self.sem_obj.V()
          pass

      return

  def init(self):
      self.shm_obj = self.create_memory(5000000)
      self.sem_obj = shm.create_semaphore(self.shm_obj.shmid, 1)
      self.sem_obj.setperm(0600)
      #self.sem_obj.setuid(quarkexec.quark_output_uid)
      self.sem_obj.setblocking(True)
      self.shm_obj.attach()
