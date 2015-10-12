#!/usr/bin/env python

import sys
from mem_file import *

if len(sys.argv) != 2:
	print """
Usage: %s <data.mem>
	""" % sys.argv[0]
	exit()

c = load_mem_file(sys.argv[1])
write_mem_file(sys.argv[1], c)
