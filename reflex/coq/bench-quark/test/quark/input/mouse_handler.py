#!/usr/bin/env python

import sys
import gobject
import threading
import gtk
from gtk import keysyms
from pymouse import PyMouseEvent
import subprocess
import time

import pygtk
pygtk.require('2.0')
import gtk, sys, cairo
from math import pi

import re

def get_focused_winid() :
    try :
        res = subprocess.check_output("xprop -id $(xprop -root | awk '/_NET_ACTIVE_WINDOW\(WINDOW\)/{print $NF}') | awk '/_NET_WM_PID\(CARDINAL\)/{print $NF}'", shell=True)
        return int(res.strip())
    except :
        return -1

output_winid = -1

def get_output_winid() :
    try :
        res = subprocess.check_output("ps aux | egrep \"python .+output.py\"", shell=True)
        splitted = re.split("[\t ]*", res.strip())
        return int(splitted[1])
    except :
        return 0

def is_in_output_win() :
    global output_winid
    #print "output_winid" + str(output_winid)
    #print get_focused_winid()
    res = (get_focused_winid() == output_winid)
    #print "output_proc:" + str(res)
    return res

def ilog(str):
    ilog_nonl(str + "\n")

def ilog_nonl(str):
    sys.stderr.write("I: " + str)
    sys.stderr.flush()

def write_char_stdout(c):
    sys.stdout.write(c)
    sys.stdout.flush()


# 65505 : RSHIFT 
# 65506 : RSHIFT 

lshift_pressed = False
rshift_pressed = False

lowercase_map = "`1234567890-=qwertyuiop[]\\asdfghjkl;'zxcvbnm,./"
uppercase_map = "~!@#$%^&*()_+QWERTYUIOP{}|ASDFGHJKL:\"ZXCVBNM<>?"

def key_pressed(keyval):
    global lshift_pressed
    global rshift_pressed

    if keyval == 65505 :
        lshift_pressed = True
        return 

    if keyval == 65506 :
        rshift_pressed = True
        return 
    
    # These have no ascii code bindings
    # 65470 ~ 645476 : 1-7 : F1-F7
    # 65477 ~ 645481 : 14-18 : F8-F12

    # 65289 : 19: TAB
    # 65293 : 20: Enter
    # 65288 : 21: Backspace

    specialMap = { 65289:'\t', 65293:'\n', 65288:'\b'}
    #funkeyMap = { 65470:1, 65471:2, 65472:3, 65473:4, 65474:5, 65475:6, 65476:7, 65477:14, 65478:15, 65479:16, 65480:17, 65481:18 }

    if keyval in specialMap :
        write_char_stdout(specialMap[keyval])
    # elif keyval in funkeyMap :
    #     out = funkeyMap[keyval]
    #     write_char_stdout(chr(out))
    elif 0 <= keyval and keyval <= 255:
        c = chr(keyval)
        # keyval is always lowercase when it's alphabet
        if lshift_pressed or rshift_pressed :
            for i in range(len(lowercase_map)) : 
                if lowercase_map[i] == c :
                    keyval = ord(uppercase_map[i])
                    break
        else :
            pass

        out = keyval
        write_char_stdout(chr(out))
    else:
        pass

class event(PyMouseEvent):
    def move(self, x, y):
        pass
        
    def keypress(self, keysym) :
        #key_pressed (keysym)
        if is_in_output_win() :
            key_pressed (keysym)


def key_released(keyval):
    global lshift_pressed
    global rshift_pressed

    if keyval == 65505 :
        lshift_pressed = False
        return 

    if keyval == 65506 :
        rshift_pressed = False
        return 

    def keyrelease(self, keysym) :
        if is_in_output_win() :
            key_released (keysym)
        
    def click(self, x, y, button, press):
        if press:
            pass
        else:
            if is_in_output_win() :
                write_char_stdout(chr(18))

e = event()
e.start()

write_char_stdout(chr(17))

import sys
import select

time.sleep(1)
output_winid = get_output_winid()

def handle_input(): 
    c = sys.stdin.read(1)
    if ord(c) == 27: 
        esc_seq = sys.stdin.read(2)
        if esc_seq == "OP": out = 1 # F1
        elif esc_seq == "OQ": out = 2 # F2
        elif esc_seq == "OQ": out = 2 # F2
        elif esc_seq == "OR": out = 3 # F3
        elif esc_seq == "OS": out = 4 # F4
        elif esc_seq == "[A": out = 19 # Up
        elif esc_seq == "[B": out = 20 # Down
        else:
            esc_seq += sys.stdin.read(2)
            if esc_seq == "[15~": out = 5 # F5
            elif esc_seq == "[17~": out = 6 # F6
            elif esc_seq == "[18~": out = 7 # F7
            elif esc_seq == "[19~": out = 14 # F8 skip ascii chars 8-13, they have meanings
            elif esc_seq == "[20~": out = 15 # F9
            elif esc_seq == "[21~": out = 16 # F10
            elif esc_seq == "[23~": out = 17 # F11 (captured by gnome for help)
            elif esc_seq == "[24~": out = 18 # F12 (mouse click)
            else: out = None
        if out != None:
            write_char_stdout(chr(out))
    else:
        write_char_stdout(c)
        
    return False

def heardEnter():
    i,o,e = select.select([sys.stdin],[],[],None)
    for s in i:
        if s == sys.stdin:
            handle_input()
    return False

#gobject.io_add_watch(sys.stdin, gobject.IO_IN, handle_input)
#gobject.io_add_watch(sys.stdin, gobject.IO_HUP, handle_hup)

#gtk.main()

if __name__ == '__main__':
    while True:
        heardEnter()
        #time.sleep(100000)        
