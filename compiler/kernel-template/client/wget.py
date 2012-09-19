#!/usr/bin/env python

import sys, os, urllib2

url = sys.argv[1]
fd  = sys.argv[2]

html = urllib2.urlopen(url).read()

f = os.fdopen(int(fd), 'w')
f.write(html)
f.close()
