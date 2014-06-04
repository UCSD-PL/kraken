#!/usr/bin/python

import select
import subprocess
import sys
import os
import socket
import shm
import threading
import time
import struct
import cairo
import array
import message
import config

#gtk.gdk.threads_init()

def olog(str):
    olog_nonl(str + "\n")

def olog_nonl(str):
    sys.stderr.write("O: " + str)
    sys.stderr.flush()

class UI:
    def main(self):
        self.message_handler = message.MessageHandler()
        self.soc = self.message_handler.KCHAN

        while (True):
            i,o,e = select.select([self.soc],[],[],None)
            m = self.message_handler.recv()
            assert m[0] == message.OpenLink, "wrong message type"
            subprocess.call(["$QUARK_CROOT/link/show.sh " + m[1]], shell=True)

UI().main()
