#!/usr/bin/env python

from mem_file import *

class Svf_generator:
	def __init__(self):
		self.last_addr = ''
		self.last_data = ''
		self.runtest_delay = 1

	def header(self):
		return """
// file header start

TRST OFF;
ENDIR IDLE;
ENDDR IDLE;
STATE RESET;
STATE IDLE;
FREQUENCY 1E6 HZ;

//Boundary Scan Chain Contents
//Position 1: xcf32p
//Position 2: xcf32p
//Position 3: xc95144xl
//Position 4: xccace
//Position 5: xc5vlx110t
TIR 48 TDI (ffffffffffff) SMASK (ffffffffffff) ;
TDR 4 TDI (00) SMASK (1f) ;	

// file header end
		"""

	def set_ctrl_reg(self, reg):
		"Program the toplevel control register"
		rv = [ 	"// set control register to %x" % reg,
				'SIR 10 TDI (3e2) SMASK (03ff) ;' ]
		rv.append("SDR 1 TDI (%x) SMASK (1) ;" % reg)
		rv.append('RUNTEST 10 TCK ;')
		return '\n'.join(rv)

	def select_mem(self, mem_name):
		self.last_addr = ''
		self.last_data = ''

		if mem_name == 'inst':
			return "// select instruction memory\nSIR 10 TDI (3c3) SMASK (03ff) ;"
		elif mem_name == 'data':
			return "// select data memory\nSIR 10 TDI (3c2) SMASK (03ff) ;"
		else:
			raise "Unknown memory '%s'" % mem_name


	def mem_access(self, addr, data):
		rv = "SDR 42 TDI (%03x%08x) SMASK (3ffffffffff) ;" % (addr, data)
		rv += "\nRUNTEST %i TCK ;" % self.runtest_delay
		self.last_addr = addr
		self.last_data = data
		return rv

	def mem_access_verify(self, addr, data, check_data):
		rv = "SDR 42 TDI (%03x%08x) SMASK (3ffffffffff) TDO (%03x%08x) MASK(3ffffffffff) ;" % (addr, data, self.last_addr, check_data)
		rv += "\nRUNTEST %i TCK ;" % self.runtest_delay
		self.last_addr = addr
		self.last_data = data
		return rv

	def mem_file(self, filename, word_size = 'word'):
		"Include instructions to transfer the contents of a .mem file"
		rv = [ "// Inserting mem file '%s'" % filename ]
		addr = 0
		if word_size == 'word':
			memimg = load_mem_file(filename, 1)
		elif word_size == 'byte':
			memimg = load_mem_file(filename, 4)
		else:
			raise 'word_size must be word or byte'

		for w in memimg:
			rv.append(self.mem_access(addr, w))
			addr = addr + 1

		rv.append("// Mem file '%s' finished" % filename)
		return '\n'.join(rv)


	def mem_file_verify_prev(self, file_new, file_old, word_size = 'word'):
		"Compare the content of filename to the current selected memory"

		if word_size == 'word':
			mem_new = load_mem_file(file_new)
			mem_old = load_mem_file(file_old)
		elif word_size == 'byte':
			mem_new = load_mem_file(file_new, 4)
			mem_old = load_mem_file(file_old, 4)
		else:
			raise 'word_size must be word or byte'

		rv = []
		for i in range(max(len(mem_new), len(mem_old)+1)):
			if i < len(mem_new):
				d_new = mem_new[i]
			else:
				d_new = 0

			if i == 0: # write the first new entry
				rv.append("SDR 42 TDI (%03x%08x) SMASK (3ffffffffff) ;" % (i, d_new))
			elif i < len(mem_old): # write new and verify old
				rv.append("SDR 42 TDI (%03x%08x) SMASK (3ffffffffff) TDO (%03x%08x) MASK(3ffffffffff) ;" % (i, d_new, i-1, mem_old[i-1]))
			else: # write new (no verify)
				rv.append("SDR 42 TDI (%03x%08x) SMASK (3ffffffffff) ;" % (i, d_new))

		return '\n'.join(rv)


	#def load_mem_file(self, filename, pack_bytes = 4):
		#"Load a mem file and return it as list. Pack pack_bytes into one word"
		#rv = []
		#f = open(filename, 'r')
		#for line in f:
			#import re

			#pack_i = pack_bytes-1
			#num = 0
			#for w in re.finditer(r"([0-9a-fA-FxX]{2})+", line):
				#if not ('x' in w.group(0) or 'X' in w.group(0)):
					#num = (int(w.group(0), 16) << (pack_i*8)) + num

				#if pack_i == 0:
					#rv.append(num)
					#pack_i = pack_bytes-1
					#num = 0
				#else:
					#pack_i = pack_i-1

			#if pack_i != pack_bytes-1:
				#rv.append(num)

		#return rv

