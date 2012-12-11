#!/usr/bin/env python
# vim: set fileencoding=utf-8
# vim: ts=4:sw=4:et:ai:sts=4

# Copyright © 2010 Martín Ferrari <martin.ferrari@gmail.com>
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the Free
# Software Foundation; either version 2 of the License, or (at your option)
# any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 51
# Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
#

import os, unittest, socket, sys, threading
from passfd import sendfd, recvfd
import _passfd

class TestPassfd(unittest.TestCase):
    def readfd_test(self, fd):
        s = os.read(fd, 512)
        self.assertEquals(s, "\0" * 512)

    def vrfy_recv(self, tuple, msg):
        self.readfd_test(tuple[0])
        self.assertEquals(tuple[1], msg)

    def parent_tests(self, s, dgram = False):
        # First message is not even sent
        s.send("1")
        self.vrfy_recv(recvfd(s), "a")
        s.send("2")
        self.vrfy_recv(recvfd(s), "\0")
        s.send("3")
        self.vrfy_recv(recvfd(s), "foobar")
        s.send("4")
        self.vrfy_recv(recvfd(s, msg_buf = 11), "long string") # is long
        if not dgram:
            self.assertEquals(s.recv(8), " is long") # re-sync
        s.send("5")
        self.assertEquals(s.recv(100), "foobar")
        s.send("6")
        self.assertRaises(RuntimeError, recvfd, s) # No fd received
        #
        s.send("7")
        f, m = recvfd(s)
        self.assertRaises(OSError, os.fdopen, f, "w")
        s.send("8")
        (f, msg) = recvfd(s)
        self.assertEquals(msg, "writing")
        os.write(f, "foo")
        s.send("9")

    def child_tests(self, s, dgram = False):
        f = file("/dev/zero")
        assert sendfd(s, f, "") == 0
        s.recv(1)
        assert sendfd(s, f, "a") == 1
        s.recv(1)
        assert sendfd(s, f, "\0") == 1
        s.recv(1)
        assert sendfd(s, f, "foobar") == 6
        s.recv(1)
        assert sendfd(s, f, "long string is long") == 19
        # The other side will recv() instead of recvmsg(), this fd would be
        # lost. I couldn't find any specification on this semantic
        s.recv(1)
        assert sendfd(s, f, "foobar") == 6
        s.recv(1)
        assert s.send("barbaz") == 6
        # Try to write!
        s.recv(1)
        assert sendfd(s, f, "writing") == 7
        s.recv(1)
        f = file("/dev/null", "w")
        assert sendfd(s, f, "writing") == 7
        s.recv(1)

    def test_sanity_checks(self):
        self.assertRaises(TypeError, recvfd, "foo")
        s = socket.socket(socket.AF_INET)
        self.assertRaises(ValueError, recvfd, s)

        (s0, s1) = socket.socketpair(socket.AF_UNIX, socket.SOCK_STREAM, 0)
        f = file("/dev/zero")
        sendfd(s0, f)
        recvfd(s1)

        # Using integers
        sendfd(s0.fileno(), f.fileno())
        recvfd(s1.fileno())

        self.assertRaises(TypeError, sendfd, s0, "foo")
        # Assuming fd 255 is not valid
        self.assertRaises(OSError, sendfd, s0, 255)

    def test_passfd_stream(self):
        (s0, s1) = socket.socketpair(socket.AF_UNIX, socket.SOCK_STREAM, 0)
        pid = os.fork()
        if pid == 0:
            s0.close()
            self.child_tests(s1)
            s1.close()
            os._exit(0)

        s1.close()
        self.parent_tests(s0)
        s0.close()

        self.assertEquals(os.waitpid(pid, 0)[1], 0)

    def test_passfd_dgram(self):
        (s0, s1) = socket.socketpair(socket.AF_UNIX, socket.SOCK_DGRAM, 0)
        pid = os.fork()
        if pid == 0:
            s0.close()
            self.child_tests(s1, dgram = True)
            s1.close()
            os._exit(0)

        s1.close()
        self.parent_tests(s0, dgram = True)
        s0.close()

        self.assertEquals(os.waitpid(pid, 0)[1], 0)

    def test_threading(self):
        # Check that the GIL is correctly released before blocking
        (s0, s1) = socket.socketpair(socket.AF_UNIX, socket.SOCK_STREAM, 0)

        def run_server(s):
            self.child_tests(s)
            s.close()

        t = threading.Thread(target = run_server, args = (s1,))
        t.start()
        self.parent_tests(s0)
        s0.close()
        t.join()

if __name__ == '__main__':
    unittest.main()

