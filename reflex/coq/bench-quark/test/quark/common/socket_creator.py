#!/usr/bin/python
import message
import sys
import socket
import passfd

message_handler = message.MessageHandler()
socket_descs = sys.argv[3].split(':')
host = socket_descs[0]
port = int(socket_descs[1])
nfamily = int(socket_descs[2])
family = socket.AF_UNIX

if nfamily == 2 :
    family = socket.AF_INET
elif nfamily == 10 :
    family = socket.AF_INET6

nsocktype = int(socket_descs[3])
socktype = socket.SOCK_SEQPACKET
if nsocktype == 1  :
    socktype = socket.SOCK_STREAM
elif nsocktype == 2 :
    socktype = socket.SOCK_DGRAM
elif nsocktype == 3 :
    socktype = socket.SOCK_RAW

s = None
for res in socket.getaddrinfo(host, port, family, socktype) :
    af, socktype, proto, canonname, sa = res
    try:
        s = socket.socket(af, socktype, proto)
    except socket.error as msg:
        s = None
        continue
    try:
        s.connect(sa)
    except socket.error as msg:
        s.close()
        s = None
        continue
    break

passfd.sendfd(message_handler.KCHAN, s.fileno(), "C")
