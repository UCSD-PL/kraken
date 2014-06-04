#!/usr/bin/python                                                                                                                                                                                           
import subprocess
import re

command = "xdpyinfo  | grep dimensions"  # the shell command                                                                                                                                                
process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=None, shell=True)
#Launch the shell command:                                                                                                                                                                                  
output = process.communicate()[0]
#print output                                                                                                                                                                                               
m = re.match(r"\s+dimensions:\s+([0-9]+)x([0-9]+)", output)

f = open("config.py", 'w')
f.write("xdimension = %s\nydimension= %s\n" % (m.group(1), m.group(2)))
