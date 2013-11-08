# -*- coding: iso-8859-1 -*-

#   Copyright 2010 Pepijn de Vos
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

from Xlib.display import Display
from Xlib import X
from Xlib.ext.xtest import fake_input
from Xlib.ext import record
from Xlib.protocol import rq


"""The goal of PyMouse is to have a cross-platform way to control the mouse.
PyMouse should work on Windows, Mac and any Unix that has xlib.

See http://github.com/pepijndevos/PyMouse for more information.
"""

from threading import Thread

class PyMouseMeta(object):

    def keypress(self, keyval):
        raise NotImplementedError

    def keyrelease(self, keyval):
        raise NotImplementedError

    def press(self, x, y, button = 1):
        """Press the mouse on a givven x, y and button.
        Button is defined as 1 = left, 2 = right, 3 = middle."""
        raise NotImplementedError

    def release(self, x, y, button = 1):
        """Release the mouse on a givven x, y and button.
        Button is defined as 1 = left, 2 = right, 3 = middle."""

        raise NotImplementedError

    def click(self, x, y, button = 1):
        """Click the mouse on a givven x, y and button.
        Button is defined as 1 = left, 2 = right, 3 = middle."""

        self.press(x, y, button)
        self.release(x, y, button)
 
    def move(self, x, y):
        """Move the mouse to a givven x and y"""

        raise NotImplementedError

    def position(self):
        """Get the current mouse position in pixels.
        Returns a tuple of 2 integers"""

        raise NotImplementedError

    def screen_size(self):
        """Get the current screen size in pixels.
        Returns a tuple of 2 integers"""

        raise NotImplementedError

class PyMouseEventMeta(Thread):
    def __init__(self, capture=False, captureMove=False):
        Thread.__init__(self)
        self.daemon = True
        self.capture = capture
        self.captureMove = captureMove
        self.state = True

    def stop(self):
        self.state = False

    def keypress(self, keyval):
        pass

    def keyrelease(self, keyval):
        pass

    def click(self, x, y, button, press):
        """Subclass this method with your click event handler"""

        pass

    def move(self, x, y):
        """Subclass this method with your move event handler"""

        pass


class PyMouse(PyMouseMeta):
    def __init__(self):
        PyMouseMeta.__init__(self)
        self.display = Display()
        self.display2 = Display()

    def keypress(self, keyval) :
        fake_input(self.display, X.KeyPress, keyval)
        self.display.sync()

    def keyrelease(self, keyval) :
        fake_input(self.display, X.KeyRelease, keyval)
        self.display.sync()

    def press(self, x, y, button = 1):
        self.move(x, y)
        fake_input(self.display, X.ButtonPress, [None, 1, 3, 2, 4, 5][button])
        self.display.sync()

    def release(self, x, y, button = 1):
        self.move(x, y)
        fake_input(self.display, X.ButtonRelease, [None, 1, 3, 2, 4, 5][button])
        self.display.sync()

    def move(self, x, y):
        fake_input(self.display, X.MotionNotify, x=x, y=y)
        self.display.sync()

    def position(self):
        coord = self.display.screen().root.query_pointer()._data
        return coord["root_x"], coord["root_y"]

    def screen_size(self):
        width = self.display.screen().width_in_pixels
        height = self.display.screen().height_in_pixels
        return width, height

class PyMouseEvent(PyMouseEventMeta):
    def __init__(self):
        PyMouseEventMeta.__init__(self)
        self.display = Display()
        self.display2 = Display()
        self.ctx = self.display2.record_create_context (
            0,
            [record.AllClients],
            [{
                    'core_requests': (0, 0),
                    'core_replies': (0, 0),
                    'ext_requests': (0, 0, 0, 0),
                    'ext_replies': (0, 0, 0, 0),
                    'delivered_events': (0, 0),
                    'device_events': (X.KeyPress, X.MotionNotify),
                    'errors': (0, 0),
                    'client_started': False,
                    'client_died': False,
            }])


    def run(self):
        if self.capture:
            self.display2.screen().root.grab_pointer(True, X.ButtonPressMask | X.ButtonReleaseMask, X.GrabModeAsync, X.GrabModeAsync, 0, 0, X.CurrentTime)

        self.display2.record_enable_context(self.ctx, self.handler)
        self.display2.record_free_context(self.ctx)

    def stop(self):
        self.display.record_disable_context(self.ctx)
        self.display.ungrab_pointer(X.CurrentTime)
        self.display.flush()
        self.display2.record_disable_context(self.ctx)
        self.display2.ungrab_pointer(X.CurrentTime)
        self.display2.flush()

    def handler(self, reply):
        data = reply.data

        while len(data):
            event, data = rq.EventField(None).parse_binary_value(data, self.display.display, None, None)            

            if event.type == X.KeyPress:
                keysym = self.display.keycode_to_keysym(event.detail, 0)
                self.keypress(keysym)
            if event.type == X.KeyRelease:
                keysym = self.display.keycode_to_keysym(event.detail, 0)
                self.keyrelease(keysym)
            if event.type == X.ButtonPress:
                self.click(event.root_x, event.root_y, (None, 1, 3, 2, 3, 3, 3)[event.detail], True)
            elif event.type == X.ButtonRelease:
                self.click(event.root_x, event.root_y, (None, 1, 3, 2, 3, 3, 3)[event.detail], False)
            else:
                self.move(event.root_x, event.root_y)
