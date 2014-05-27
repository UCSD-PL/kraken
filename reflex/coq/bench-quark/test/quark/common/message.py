import socket, os, os.path, sys, re, time
import struct, passfd, atexit

# Input -> Kernel
TabCreate   = 0
TabSwitch   = 1

# Input -> Kernel -> (focused) Tab
Navigate    = 2
KeyPress    = 3
MouseClick  = 4

# Kernel -> Input
AddrAdd  = 5

# Tab -> Kernel -> Screen
RenderCompleted = 6

# Kernel -> Tab
RenderRequest = 7

# Tab -> Kernel
URLRequest = 8

# Kernel -> Tab
URLResponse = 9

# Tab -> Kernel
SocketRequest = 10

# Kernel -> Tab (Sending out a socket to a CreateSocket.py process)
SocketResponse = 11

# Tab -> Kernel
CookieChannelInit = 12

# Kernel -> Cookie 
TabProcessRegister = 13

# Kernel -> Input
AddrFocus  = 14

DomainSet = 15

# Kernel -> Link
OpenLink = 16

# Tab -> Cookie
CookieJarRequest = 17

# Cookie -> Tab
CookieJarResponse = 18

# Tab -> Cookie
CookieUpdate = 19

# Cookie -> Tabs
CookieBroadcast = 20



class MessageHandler(object) :
    FD    = None
    KCHAN = None
    PROG  = None
    LOG   = None

    def __init__(self, soc = None) :
        self.FD = soc.fileno() if soc != None else int(sys.argv[1])
        if soc == None :
            # this is the standard out, used for debugging
            if self.FD == 1 :
                class FDWrapper :
                    def recv(self, n) :
                        return None
                    def send(self, s) :
                        print s
                self.KCHAN = FDWrapper()
            else :
                self.KCHAN = socket.fromfd(self.FD, socket.AF_UNIX, socket.SOCK_STREAM)
        else :
            self.KCHAN = soc

        # set up logging
        self.PROG = os.path.basename(sys.argv[0])
        self.path = os.path.join(os.environ['QUARK_CROOT'], 'log', '%s-%d-log' % (self.PROG, self.FD))
        self.LOG  = open(self.path, 'w', 0) # unbuffered

        if soc == None :
            # tear down at exit
            atexit.register(lambda: self.KCHAN.close())
            atexit.register(lambda: self.LOG.close())
        
    def log(self, msg):
        pass
        #self.LOG.write('%15s @ %f || %s\n' %
        #               ('%s(%d)' % (self.PROG, self.FD - 1), time.time(), msg))

    def recv_num(self):
        # TODO(d1jang): Is 2 bytes enough?
        s = self.KCHAN.recv(2)
        n = struct.unpack('>H', s)[0]
        return n

    def recv_str(self):
        n = self.recv_num()
        if n > 0 :
            s = self.KCHAN.recv(n)
        else :
            s = ""
        return s

    def recv_fd(self):
        fd, _ = passfd.recvfd(self.KCHAN)
        f = os.fdopen(fd, 'r')
        return f

    def send_num(self, n):
        s = struct.pack('>H', n)
        self.KCHAN.send(s)

    def send_str(self, s):
        self.send_num(len(s))
        self.KCHAN.send(s)

    def send_fd(self, f):
        fd = f.fileno()
        passfd.sendfd(self.KCHAN, fd, "C")

    def msg_str(self, m):
        def param_str(p):
            if isinstance(p, int):
                return '%d' % p
            elif isinstance(p, str):
                p = re.escape(p)
                p = p.replace('\n', '\\n')
                return '"%s"' % p
            else:
                # assume fd
                return 'fd(%d)' % p.fileno()
        params = ", ".join(map(param_str, m[1:]))
        return '%s(%s)' % (m[0], params)

    def recv(self):
        tag = self.recv_num()
        print "%d is received" % tag
        m = {
            # (tab_id,domain)
            0 : lambda : [TabCreate, self.recv_str(),self.recv_str()],
            # tab_id
            1 : lambda : [TabSwitch, self.recv_str()],
            2 : lambda : [Navigate, self.recv_str()],
            3 : lambda : [KeyPress, self.recv_str()],
            4 : lambda : [MouseClick, self.recv_str()],
            # (tab_id, domain)
            5 : lambda : [AddrAdd, self.recv_str(),self.recv_str()],
            6 : lambda : [RenderCompleted, self.recv_str()],
            7 : lambda : [RenderRequest, self.recv_str()],
            #7 : lambda : [RenderRequest, " "],
            8 : lambda : [URLRequest, self.recv_str()],
            9 : lambda : [URLResponse, self.recv_fd()],
            10 : lambda : [SocketRequest, self.recv_str()],
            11 : lambda : [SocketResponse, self.recv_fd()],
            12 : lambda : [CookieChannelInit, self.recv_fd()],
            13 : lambda : [TabProcessRegister, self.recv_fd()],
            # tab_id
            14 : lambda : [AddrFocus, self.recv_str()],
            15 : lambda : [DomainSet, self.recv_str()],
            16 : lambda : [OpenLink, self.recv_str()],
            17 : lambda : [CookieJarRequest, self.recv_str()],
            18 : lambda : [CookieJarResponse, self.recv_str()],
            19 : lambda : [CookieUpdate, self.recv_str()],
            20 : lambda : [CookieBroadcast, self.recv_str()]
            } [tag] ()
        self.log('recv : %s(%s)' % (m[0], m[1]))
        return m

    def send(self, m):
        tag = m[0]
        #print "%d is sent:" % tag
        {
            TabCreate   : lambda : [self.send_num(0), self.send_str(m[1]), self.send_str(m[2])],
            TabSwitch   : lambda : [self.send_num(1), self.send_str(m[1])],
            Navigate    : lambda : [self.send_num(2), self.send_str(m[1])],
            KeyPress    : lambda : [self.send_num(3), self.send_str(m[1])],
            MouseClick  : lambda : [self.send_num(4), self.send_str(m[1])],
            AddrAdd  : lambda : [self.send_num(5), self.send_str(m[1]), self.send_str(m[2])],
            RenderCompleted : lambda : [self.send_num(6), self.send_str(m[1])],
            RenderRequest : lambda : [self.send_num(7), self.send_str(m[1])],
            URLRequest : lambda : [self.send_num(8), self.send_str(m[1])],
            URLResponse : lambda : [self.send_num(9), self.send_fd(m[1])],
            SocketRequest : lambda : [self.send_num(10), self.send_str(m[1])],
            SocketResponse : lambda : [self.send_num(11), self.send_fd(m[1])],
            CookieChannelInit : lambda : [self.send_num(12), self.send_fd(m[1])],
            TabProcessRegister : lambda : [self.send_num(13), self.send_fd(m[1])],
            AddrFocus : lambda : [self.send_num(14), self.send_str(m[1])],
            DomainSet : lambda : [self.send_num(15), self.send_str(m[1])],
            OpenLink : lambda : [self.send_num(16), self.send_str(m[1])],
            CookieJarRequest : lambda : [self.send_num(17), self.send_str(m[1])],
            CookieJarResponse : lambda : [self.send_num(18), self.send_str(m[1])],
            CookieUpdate : lambda : [self.send_num(19), self.send_str(m[1])],
            CookieBroadcast : lambda : [self.send_num(20), self.send_str(m[1])]
         }[tag]()
        self.log('send : %s(%s)' % (m[0], m[1]))
