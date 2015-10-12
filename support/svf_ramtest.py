#!/usr/bin/env python

import random
from svf_generator import *


def ramtest():
	svf_gen = Svf_generator()
	svf = []
	test_img = [ random.randint(0, 2**32-1) for i in range(1024) ]

	svf.append(svf_gen.header())
	svf.append(svf_gen.set_ctrl_reg(1))  # reset on
	svf.append(svf_gen.select_mem('data'))

	# write data
	addr = 0
	for w in test_img:
		svf.append(svf_gen.mem_access(addr, w))
		addr = addr + 1

	# verify data
	addr = 0
	last_w = 0
	for w in test_img:
		if addr == 0:
			svf.append(svf_gen.mem_access(addr, w+1))
		else:
			svf.append(svf_gen.mem_access_verify(addr, w+1, last_w))

		last_w = w

		addr = addr + 1

	print '\n'.join(svf)


for i in range(100):
	ramtest()
