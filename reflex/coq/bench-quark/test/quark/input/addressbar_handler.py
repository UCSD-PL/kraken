import sys, getopt
import select
import threading
import debugmode
import message
import subprocess
import re

_tab_switch_map = {"OP":0, "OQ":1, "OR":2, "OS":3, "[15~":4, "[17~":5, "[18~":6, "[19~":7, "[20~":8, "[21~":9,}
_new_tab_map = {"[24~":0}
#_scroll_map = {"[A":0, "[B":1}
#_all_map = dict(_tab_switch_map.items() + _new_tab_map.items() + _scroll_map.items())
_all_map = dict(_tab_switch_map.items() + _new_tab_map.items())

class AddressBarHandler(threading.Thread) :
    message_handler = None

    NEWTAB_EVENT = 0
    TAB_SWITCH_EVENT = 1
    CHAR_EVENT = 2

    char_buf = []
    addrs = []
    curaddr = None
    focused_tabid = None

    class AddressBarEvent :
        event_type = None
        event_value = None
        def __init__(self, event_type, event_value) :
            self.event_type = event_type
            self.event_value = event_value

    def __init__(self, message_handler) :
        threading.Thread.__init__(self)
        self.char_buf = []
        self.addrs = []
        self.message_handler = message_handler
        self.curaddr = None
        self.echo_off()
        self.refresh()

    def interpret_fkey(self, esc_seq) :
        if esc_seq in _new_tab_map :
            return self.AddressBarEvent(self.NEWTAB_EVENT, _new_tab_map[esc_seq])
        elif esc_seq in _tab_switch_map :
            #print "tab switch " + str(_tab_switch_map[esc_seq])
            return self.AddressBarEvent(self.TAB_SWITCH_EVENT, _tab_switch_map[esc_seq])
        else :
            raise "non-reachable"

    def interpret_input(self): 
        c = sys.stdin.read(1)
        if ord(c) == 27: 
            esc_seq = sys.stdin.read(2)
            if esc_seq in _all_map :
                return self.interpret_fkey(esc_seq)
            else:
                esc_seq += sys.stdin.read(2)
                if esc_seq in _all_map :
                    return self.interpret_fkey(esc_seq)
                else :
                    return None
        else:
            return self.AddressBarEvent(self.CHAR_EVENT, c)

    def refresh(self) :
        #subprocess.call("clear")
        print "-------------------------------------------------------------------------------------------------------------"
        addr_strs = []
        for addr in self.addrs :
            raw_addr = addr[1]
            if addr[0] == self.focused_tabid :
                raw_addr = "\033[95m" + raw_addr + "\033[0m"
            addr_strs.append(raw_addr)
        print " | ".join([addr for addr in addr_strs])
        print "-------------------------------------------------------------------------------------------------------------"

    def echo_on(self) :
        subprocess.call(["stty","-cbreak", "echo"])

    def echo_off(self) :
        subprocess.call(["stty","cbreak", "-echo"])

    def run(self):
        while True :
            i,o,e = select.select([sys.stdin] + [self.message_handler.KCHAN],[],[],None)
            for s in i:
                if s == self.message_handler.KCHAN :
                    print "sth is receved from kernel:"
                    m = self.message_handler.recv()
                    print m
                    if m[0] == message.AddrAdd :
                        # (id,domain)
                        print "addr add-1"
                        self.addrs.append((m[1],m[2]))
                        self.focused_tabid = m[1]
                        print "addr add-2"
                    elif m[0] == message.AddrFocus :
                        print "address focus:'" + m[1] + "'"
                        self.focused_tabid = m[1]
                    self.refresh()
                elif s == sys.stdin:
                    event = self.interpret_input()
                    if event == None : continue
                    elif event.event_type == self.NEWTAB_EVENT :
                        debugmode.printmsg("NEWTAB_EVENT")
                        self.echo_on()
                        while True :
                            print "Enter the trusted domain for a new tab(e.g.,a.com):"
                            domain = raw_input("")
                            # if the domain is not a top-level domain, take the top domain out of it.
                            m = re.search("\w+\.\w+$",domain)
                            if m == None : continue
                            domain = m.group()
                            break
                        self.echo_off()
                        self.message_handler.send([message.TabCreate, ("%d.%s" % (len(self.addrs),str(domain))), str(domain)])
                        print "done well"
                    elif event.event_type == self.TAB_SWITCH_EVENT :
                        print "tab switching:" + str(self.addrs)
                        debugmode.printmsg("TAB_SWITCH_EVENT" + self.addrs[int(event.event_value)][0])
                        self.message_handler.send([message.TabSwitch, self.addrs[int(event.event_value)][0]])
                    elif event.event_type == self.CHAR_EVENT : 
                        debugmode.printmsg("CHAR_EVENT")
                        if event.event_value == '\n' :
                            if self.curaddr != None and "".join(self.char_buf).find(self.curaddr) != -1:
                                self.message_handler.send([message.Navigate, "".join(self.char_buf)])
                            self.char_buf = []
                            self.refresh()
                            continue
                        else :
                            if event.event_value == '\x7f' and len(self.char_buf) > 0 :
                                self.char_buf = self.char_buf[0:len(self.char_buf) - 1]
                            else :
                                self.char_buf.append(event.event_value)
                        # TODO(d1jang): this is a hacking to
                        # remove all the characters in the same
                        # line, and should be improved.
                        sys.stdout.write("\r                                 ")
                        sys.stdout.write("\r%s" % ("".join(self.char_buf)))
                        sys.stdout.flush()
                    else :
                        sys.stderr.write('invalid event type\n')
                        sys.exit(1)

if __name__ == '__main__':
    handler = AddressBarHandler()
    handler.start()
