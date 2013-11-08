#!/usr/bin/python

import string
import sys
import subprocess
import select
import cPickle as pickle
import socket
import Cookie
import datetime
import signal
import message
import opt
import os
import stat

def signal_handler(signal, frame):
    c.exit()
    sys.exit(0)

def clog(str):
    clog_nonl(str + "\n")

def clog_nonl(str):
    sys.stderr.write("C: " + str)
    sys.stderr.flush()
    
class CookieManager:
    tabs = []

    def __init(self) :
        self.tabs = []
    
    def cookies_for_domain(self, domain):
        if domain in self.cookie_db:
            return self.cookie_db[domain]
        else:
            cookies = Cookie.SimpleCookie()
            self.cookie_db[domain] = cookies
            return cookies

    def add_cookie(self, cookie_str):        
        def get_domain(cookie_str):
            c = Cookie.SimpleCookie()
            c.load(cookie_str)
            for name in c:
                return c[name]['domain']
        try :
            domain = get_domain(cookie_str)
            cookies = self.cookies_for_domain(domain)
            cookies.load(cookie_str)
        except :
            clog("an error occured while adding a cookie string" + str(sys.exc_info()))

    def get_cookies(self, scheme, domain, path, for_http):
        result_list = []
        def add_cookies_for_domain(domain):
            if domain in self.cookie_db:
                cookies = self.cookie_db[domain]
                # note: "for name in cookies" crashes because of 
                # "modification during iteration"
                for name in cookies.keys(): 
                    if cookie_expired(cookies[name]):
                        del cookies[name]
                    else:
                        #if cookie_matches_scheme(cookies[name], scheme) and \
                        #   cookie_matches_path(cookies[name], path) and \
                        #   cookie_matches_for_http(cookies[name], for_http)   :
                        if cookie_matches_scheme(cookies[name], scheme) and \
                           cookie_matches_path(cookies[name], path) :
                            #result_list.append(name + "=" + cookies[name].value + "; path=" + cookies[name]['path'] + "; domain=" + cookies[name]['domain'] + ("; secure=" + cookies[name]['secure'] if cookies[name]['secure'] <> '' else '') +  ("; httponly=" + cookies[name]['httponly'] if cookies[name]['httponly'] <> '' else ''))
                            result_list.append(name + "=" + cookies[name].value + ("; expires=" + cookies[name]['expires'] if cookies[name]['expires'] <> '' else '')+ "; path=" + cookies[name]['path'] + "; domain=" + domain + ("; secure=" + cookies[name]['secure'] if cookies[name]['secure'] <> '' else '') +  ("; httponly=" + cookies[name]['httponly'] if cookies[name]['httponly'] <> '' else ''))
        # Comment and logic copied from libsoup:
	# The logic here is a little weird, but the plan is that if
	# domain is "www.foo.com", we will end up looking up cookies
	# for ".www.foo.com", "www.foo.com", ".foo.com", and ".com",
	# in that order. (Logic stolen from Mozilla.)
	l = domain.split(".")
        while l != []:
            domain_try = ".".join(l)
            #clog("domain_try:" + domain_try);
            #clog("Trying domain: ." + domain_try)
            add_cookies_for_domain("." + domain_try)
            if domain_try == domain:
                #clog("Trying domain: " + domain_try)
                add_cookies_for_domain(domain_try)
                #clog("Result_list: " + str(result_list))
            l = l[1:]
        #clog("Result_list: " + str(result_list))
        if result_list == []:
            return " "
        else:
            return '@@@ '.join(result_list) + ' @@@'

    def run(self):
        #self.soc = socket.fromfd(int(sys.argv[1]), msg.FAMILY, msg.TYPE)
        print sys.argv
        self.message_handler = message.MessageHandler()
        self.ksock = self.message_handler.KCHAN

        print "cookie initialization:begin"
        m = self.message_handler.recv()
        assert m[0] == message.DomainSet
        self.name = m[1]
        print "cookie initialization:end:%s" % self.name
        #opt.parse_options(sys.argv[3:])

        try:
            f = open("cookies/" + self.name)
            self.cookie_db = pickle.load(f)
            f.close
        except : 
            clog("cookie file loading failed")
            self.cookie_db = {}

        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)
        signal.signal(signal.SIGABRT, signal_handler)

        while (True):
            i,o,e = select.select(self.tabs + [self.ksock],[],[],None)
            print "cookie %s received a message " % self.name
            for s in i:
                message_handler = message.MessageHandler(s)
                m = message_handler.recv()
                mtype = m[0]

                if s == self.ksock :
                    if mtype == message.TabProcessRegister :
                        print "message : %s " % str(m[1])
                        self.tabs.append(socket.fromfd(m[1].fileno(), socket.AF_UNIX, socket.SOCK_STREAM))
                    else :
                        sys.stderr.write("Invalid message type from kernel :%d " % mtype)
                        #sys.exit(1)
                        c.exit()
                elif mtype == message.CookieJarRequest : 
                    # this is not a uri. this is a formatted data string by the tab
                    data = m[1]
                    idx = string.find(data, ";")
                    first = data[0:idx]

                    idx2 = string.find(data, ";", idx + 1)
                    second = data[idx + 1 : idx2]

                    idx3 = string.rfind(data, ";")
                    third = data[idx2 + 1 : idx3]
          
                    fourth = data[idx3 + 1:] 
                    cookies = self.get_cookies(first,second,third, bool(int(fourth)))
                    print "cookie process sends :%d" % len(cookies)
                    message.MessageHandler(s).send(
                        [message.CookieJarResponse, cookies])
                elif mtype == message.CookieUpdate : 
                    self.add_cookie(m[1])
                    for t in self.tabs : 
                        if t != s : 
                            message.MessageHandler(s).send(
                                [message.CookieBroadcast, m[1]])
                else :
                    sys.stderr.write("Invalid message type :%d " % mtype)
                    sys.exit(1)

    def exit(self):
        for domain in self.cookie_db:
            cookies = self.cookie_db[domain]
            # note: "for name in cookies" crashes because of 
            # "modification during iteration"
            for name in cookies.keys(): 
                if cookie_expired_at_exit(cookies[name]):
                        del cookies[name]
        try:
            os.mkdir("cookies")
        except:
            pass
        try:
            f = open("cookies/" + self.name, "w")
            pickle.dump(self.cookie_db, f)
            f.close()
            os.chmod("cookies/" + self.name, stat.S_IRUSR | stat.S_IWUSR)
        except IOError as e:
            pass            
        sys.exit(0)

def cookie_expired(cookie):
    expires_str = cookie["expires"]
    if expires_str == "":
        # this is a session cookie, is not expired (will expire when
        # browser exits)
        return False
    else:
        expires = datetime.datetime.strptime(expires_str, "%a, %d-%b-%Y %H:%M:%S GMT")
        now = datetime.datetime.now()
        return expires < now

def cookie_expired_at_exit(cookie):
    expires_str = cookie["expires"]
    if expires_str == "":
        # this is a session cookie, it's expired since browser exits
        return True
    else:
        expires = datetime.datetime.strptime(expires_str, "%a, %d-%b-%Y %H:%M:%S GMT")
        now = datetime.datetime.now()
        return expires < now

def cookie_matches_scheme(cookie, scheme):
    return scheme == "https" or not cookie["secure"] == "true"
    
def cookie_matches_path(cookie, path):
    # following logic from soup_cookie_applies_to_uri in soup-cookie.c
    cookie_path = cookie["path"]
    if cookie_path == "":
        return True
    if not path.startswith(cookie_path):
        return False
    if not cookie_path.endswith("/") and len(path) > len(cookie_path) and path[len(cookie_path)] != "/":
        return False
    return True

def cookie_matches_for_http(cookie, for_http):
    return for_http or not cookie["httponly"] == "true"

c = CookieManager()
c.run()

