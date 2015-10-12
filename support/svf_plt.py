#!/usr/bin/env python

from svf_generator import *


def make_test(name, duration = 500000, path = '', data_file = ''):
	"Make a dictionary describing the test. Duration is in us"

	if data_file != '':
		dfile = data_file
	else:
		dfile = "%s%s.mem" % (path, name)

	return { 'code': "%s%s_code.mem" % (path, name),
			 'data': dfile,
			 'exp' : "%s%s_exp.mem" % (path, name),
			 'duration': duration }


tests = {
	'load_add_store' : make_test('load_add_store'),
	'branch'         : make_test('branch', data_file = 'empty.mem'),
	'branch_cond'    : make_test('branch_cond', data_file = 'empty.mem'),
	'simple_interlock_test': make_test('simple_interlock_test'),
	'interlocks'     : make_test('interlocks'),
	'logic'          : make_test('logic', data_file = 'empty.mem')
}



def multi_prog_test(svf, test_list, testcode_path = 'test/testcode/'):
	svf_gen = Svf_generator()

	svf.append(svf_gen.header())

	exp_mem_prev = ''

	for name, test in test_list.items():
		svf.append("//\n// *** BEGIN: %s ***\n//\n" % name)
		svf.append(svf_gen.set_ctrl_reg(1))  # reset on
		svf.append(svf_gen.select_mem('inst'))
		svf.append(svf_gen.mem_file(testcode_path + test['code'], word_size='word'))
		svf.append(svf_gen.select_mem('data'))

		if exp_mem_prev == '':
			svf.append(svf_gen.mem_file(testcode_path + test['data'], word_size='byte'))
		else:
			svf.append(svf_gen.mem_file_verify_prev(testcode_path + test['data'], exp_mem_prev, word_size='byte'))
		exp_mem_prev = testcode_path + test['exp']

		svf.append(svf_gen.set_ctrl_reg(0))  # reset off
		svf.append("RUNTEST %i TCK ;" % test['duration'])
		svf.append("//\n// *** END: %s ***\n//\n" % name)

def single_prog_test(svf):
	svf_gen = Svf_generator()

	svf.append(svf_gen.header())
	svf.append(svf_gen.set_ctrl_reg(1))  # reset on
	svf.append("RUNTEST 100000 TCK ;")
	svf.append(svf_gen.set_ctrl_reg(0))  # reset off
	svf.append("RUNTEST 1000000 TCK ;")


svf = []
#multi_prog_test(svf, tests)
for i in range(10):
	single_prog_test(svf)
print '\n'.join(svf)


