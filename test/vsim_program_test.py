#!/usr/bin/env python

import os
import shutil

def compile_program(name, codepath, respath):
	os.system("../support/compile_asm.sh %s/%s.s %s/%s_code.mem" % (codepath, name, respath, name))


def run_test(name, respath, data_file):

	os.system("vmap work ../work")

	do_script = """
onerror resume
add mem /Pu_test/uut/inst_fetch/imem -a hexadecimal -d hexadecimal
add mem /Pu_test/uut/load_store/mem -a hexadecimal -d hexadecimal

mem load -i %s/%s_code.mem -format hex /Pu_test/uut/inst_fetch/imem
mem load -i %s/%s -format mti /Pu_test/uut/load_store/mem

run 1 us
""" % (respath, name, respath, data_file)

	file = open("%s/run_test.do" % respath, "w")
	file.write(do_script)
	file.close()

	os.system("vsim work.Pu_test -novopt -do %s/run_test.do" % respath)
	os.unlink("%s/run_test.do" % respath)


codepath = "./testcode"
respath = "./test_build"

tests = [ 
	[ "load_add_store", "load_add_store.mem" ]
]

data = { 'in': 'load_add_store.mem' }

if not os.access(codepath, os.F_OK or os.R_OK):
	raise Exception("No access to directory '%s'!" % codepath)

if not os.access(respath, os.F_OK or os.W_OK):
	os.mkdir(respath)
	
	if not os.access(respath, os.F_OK or os.W_OK):
		raise Exception("No access to directory '%s'!" % respath)

for i in tests:
	print("Compiling %s" % i[0])
	compile_program(i[1], codepath, respath)

for k,i in data.items():
	print("Copying data file %s/%s -> %s/%s" % (codepath, i, respath, i))
	shutil.copy("%s/%s" % (codepath, i), "%s/%s" % (respath, i))

for i in tests:
	print("Running %s" % i[0] )
	run_test(i[1], respath, i[1])

