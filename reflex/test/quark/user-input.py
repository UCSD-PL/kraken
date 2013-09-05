#!/usr/bin/env python2.7

import msg, readline, time
from gtk import keysyms
from pymouse import PyMouseEvent

class event(PyMouseEvent):
    def move(self, x, y):
        pass
        
    def keypress(self, keysym) :
        pass
        #if 0 <= keysym and keysym <= 256 :
        #    print "KeyPress", chr(keysym)
        #key_pressed (keysym)
        #if is_in_output_win() :
        #    key_pressed (keysym)

    def keyrelease(self, keysym) :
        msg.send(msg.KeyPress, str(keysym))
        #if 0 <= keysym and keysym <= 256 :
        #   print "KeyRelease", chr(keysym)
        #key_released (keysym)
        #if is_in_output_win() :
        #    key_released (keysym)
        
    def click(self, x, y, button, press):
        if press:
            msg.send(msg.MouseClick, str(x), str(y), 1)
        else:
            msg.send(msg.MouseClick, str(x), str(y), 0)
        #if press:
        #    pass
        #else:
        #    if is_in_output_win() :
        #       write_char_stdout(chr(18))

def main():
  msg.init()
  e = event()
  e.start()
  try:
    while True:
      #uin = raw_input("\n")
      #if uin == ':new':
      #    pass
          #msg.send(msg.NewTab)
      #else:
#        msg.send(msg.KeyPress, uin)
          pass
  except EOFError:
    pass
    #msg.send('Quit')

main()
