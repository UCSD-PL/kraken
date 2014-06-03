import sys, getopt
import os

#debug = True if "QUARK_DEBUG" in os.environ else False
debug = False

if debug :
    print "debug mode is on"

def printmsg(str) :
    if debug : print str
    
