#!/usr/bin/env python

import sys
from svf_generator import *

if len(sys.argv) == 1:
	print """
Usage: svf_programmer.py <code.mem> [<data.mem>]
	"""
	exit()

def program(svf, code, data = ''):
	svf_gen = Svf_generator()

	svf.append(svf_gen.header())
	svf.append(svf_gen.set_ctrl_reg(1))  # hold processor
	svf.append(svf_gen.select_mem('inst'))
	svf.append(svf_gen.mem_file(code, word_size='word'))
	if data != '':
		svf.append(svf_gen.select_mem('data'))
		svf.append(svf_gen.mem_file(data, word_size='byte'))

	svf.append(svf_gen.set_ctrl_reg(0))  # unhold processor

svf = []
if len(sys.argv) == 2:
	program(svf, sys.argv[1])
else:
	program(svf, sys.argv[1], sys.argv[2])

# svf_gen = Svf_generator()
# svf.append(svf_gen.header())
# svf.append(svf_gen.select_mem('inst'))
# svf.append(svf_gen.mem_file_verify_prev(sys.argv[1], sys.argv[2]))

# svf_gen = Svf_generator()
# print svf_gen.load_mem_file('../test/testcode/c/eblinker_data.mem')

print '\n'.join(svf)
