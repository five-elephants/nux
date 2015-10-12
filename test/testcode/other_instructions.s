# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


###########################################################
# other_instruction.s
#
# Test various instructions that are only rarely used
###########################################################

.include "macros.s"

start:
	li 15, 0xff
	li 16, 0x00

	# write 0x00_ff_00_ff to first word in memory
	stb 16, 0(0)
	stb 15, 1(0)
	stb 16, 2(0)
	stb 15, 3(0)
	
	lwz 17, 0(0)	      # load first word from memory
	rotrwi 17, 17, 8      # rotate word by 8 bits to the right
	stw 17, 1*4(0)        # store mem[1] = 0xff_00_ff_00

	# test sign extension
	lhz 17, 1*4+2(0)      # load 0xff00 from memory
	extsb 18, 15          # extend sign of 0xff -> 0xff_ff_ff_ff
	extsb 19, 16          # extend sign of 0x00 -> 0x00_00_00_00
	extsh 20, 15          # extend sign 0f 0x00_ff -> 0x00_00_00_ff
	extsh 21, 17          # extend sign of 0xff_00 -> 0xff_ff_ff_00
	extsb 22, 17          # extend sign of 0x00 -> 0x00_00_00_00

	# store results
	stw 18, 2*4(0)
	stw 19, 3*4(0)
	stw 20, 4*4(0)
	stw 21, 5*4(0)
	stw 22, 6*4(0)

	# test population count
	lwz 15, 0(0)
	lwz 16, 4(0)
	li 17, 0x1234
	oris 17, 17, 0xf073

	my_popcntb 23, 15     # count ones per byte 0x00ff00ff -> 0x00080008
	my_popcntb 24, 16     # count ones per byte 0xff00ff00 -> 0x08000800
	my_popcntb 25, 17     # count ones per byte 0xf0731234 -> 0x04050203

	stw 23, 7*4(0)
	stw 24, 8*4(0)
	stw 25, 9*4(0)

	# test parity instruction
	li 15, 0x0803
	lis 16, 0x7000
	my_prtyw 23, 23       # calculate parity of 0x00ff00ff -> 0
	my_prtyw 24, 24       # calculate parity of 0xff00ff00 -> 0
	my_prtyw 25, 25       # calculate parity of 0xf0731234 -> 0

	my_popcntb 26, 15     
	my_popcntb 27, 16
	my_prtyw 26, 26       # calculate parity of 0x0003 -> 1
	my_prtyw 27, 27       # calculate parity of 0x7000_0000 -> 1

	stw 23, 10*4(0)
	stw 24, 11*4(0)
	stw 25, 12*4(0)
	stw 26, 13*4(0)
	stw 27, 14*4(0)

end:
	my_wait

	nop
	nop
	nop
