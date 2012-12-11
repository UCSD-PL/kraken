#!/usr/bin/env python2.7
# vim: set fileencoding=utf-8
# vim: ts=4:sw=4:et:ai:sts=4
from distutils.core import setup, Extension
import sys
sys.path.append("src")
import passfd

module1 = Extension('_passfd', sources = ['src/passfd.c'])

setup(
        name        = 'python-passfd',
        version     = '0.2',
        description = 'Python functions to pass file descriptors across ' +
        'UNIX domain sockets',
        long_description = passfd.__doc__,
        author      = 'Martin Ferrari',
        author_email = 'martin.ferrari@gmail.com',
        url         = 'http://code.google.com/p/python-passfd/',
        license     = 'GPLv2',
        platforms   = 'Linux',
        package_dir = {'': 'src'},
        ext_modules = [module1],
        py_modules  = ['passfd'])
