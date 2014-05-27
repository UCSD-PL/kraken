import subprocess
import re
import os
import pymouse
import debugmode
import message

class OutputWindowTracker(object) : 
    @staticmethod
    def get_output_winid(process_name) :
        try :
            res = subprocess.check_output("ps aux | egrep \"python .+%s\"" % (process_name), shell=True)
            splitted = re.split("[\t ]*", res.strip())
            return int(splitted[1])
        except :
            return 0

    @staticmethod
    def get_focused_winid() :
        try :
            res = subprocess.check_output("xprop -id $(xprop -root | awk '/_NET_ACTIVE_WINDOW\(WINDOW\)/{print $NF}') | awk '/_NET_WM_PID\(CARDINAL\)/{print $NF}'", shell=True)
            return int(res.strip())
        except :
            return -1

    win_id = None

    def __init__(self, process_name="output.py") :
        self.win_id = OutputWindowTracker.get_output_winid(process_name)
    
    def focused(self) :
        return OutputWindowTracker.get_focused_winid() == self.win_id

class ScreenHandler(pymouse.PyMouseEvent):
    message_handler = None
    lshift_pressed = False
    rshift_pressed = False
    screen_tracker = None

    lowercase_map = "`1234567890-=qwertyuiop[]\\asdfghjkl;'zxcvbnm,./"
    uppercase_map = "~!@#$%^&*()_+QWERTYUIOP{}|ASDFGHJKL:\"ZXCVBNM<>?"

    def __init__(self, message_handler) :
        pymouse.PyMouseEvent.__init__(self)
        self.message_handler = message_handler
        self.screen_tracker = OutputWindowTracker()
        self.lshift_pressed = False
        self.rshift_pressed = False

    def move(self, x, y):
        pass
        
    def keyrelease(self, keysym) :
        if self.screen_tracker.focused() : self.key_released (keysym)

    def keypress(self, keysym) :
        if self.screen_tracker.focused() : self.key_pressed (keysym)

    def key_released(self, keyval):
        if keyval == 65505 :
            self.lshift_pressed = False
        elif keyval == 65506 :
            self.rshift_pressed = False

    def key_pressed(self, keyval):
        if keyval == 65505:
            self.lshift_pressed = True
            return 
        if keyval == 65506:
            self.rshift_pressed = True
            return 
        
        #print "keyval:" + str(keyval)
    
        specialMap = { 65289:'\t', 65293:'\n', 65288:'\b'}
        rawMap = { 65362:19, 65364: 20 }

        if keyval in specialMap :
            self.message_handler.send([message.KeyPress, str(specialMap[keyval])])
        elif keyval in rawMap :
            self.message_handler.send([message.KeyPress, str(chr(rawMap[keyval]))])
        elif 0 <= keyval and keyval <= 255:
            c = chr(keyval)
            # keyval is always lowercase when it's alphabet
            if self.lshift_pressed or self.rshift_pressed :
                for i in range(len(self.lowercase_map)) : 
                    if self.lowercase_map[i] == c :
                        keyval = ord(self.uppercase_map[i])
                        self.message_handler.send([message.KeyPress, str(chr(keyval))])
                        return
            self.message_handler.send([message.KeyPress, str(c)])

    def click(self, x, y, button, press):
        if not press and self.screen_tracker.focused() :
            line = os.popen("xwininfo -name 'Quark Web Browser Output'").read()
            m = re.search("Absolute upper-left X:(\s+)(\S+)(\s+)Absolute upper-left Y:(\s+)(\S+)", line)
            outputx = int(m.group(2))
            outputy = int(m.group(5))
            self.message_handler.send([message.MouseClick, ("%d:%d" % (x - outputx,y - outputy))])

if __name__ == '__main__':
    screen_handler = ScreenHandler()
    screen_handler.start()
