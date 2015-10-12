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
# cr_complex.s 
#
# Test some of the more advanced instruction variants using
# CR field.
###########################################################

.include "macros.s"

.macro crf_xor ft, fa, fb
	crxor (4* \ft )+0, (4* \fa )+0, (4* \fb )+0
	crxor (4* \ft )+1, (4* \fa )+1, (4* \fb )+1
	crxor (4* \ft )+2, (4* \fa )+2, (4* \fb )+2
	crxor (4* \ft )+3, (4* \fa )+3, (4* \fb )+3
.endm

start:
	lhz 1, 0(0)           # load pointer to input list
	lhz 2, 2(0)           # load pointer to output list
	lmw 24, 0(1)          # load input list from pointer

	mr 5, 2
	bl sort_pairs

	# test CR logical instructions
	li 15, 0xa
	li 16, 0xb
	li 17, 0x3
	li 18, 0x9
	# move to correct bit positions
	insrwi 15, 15, 4, 4*4
	insrwi 16, 16, 4, 5*4
	insrwi 17, 17, 4, 6*4
	insrwi 18, 18, 4, 7*4
	# move to CR fields
	mtocrf 0b00001000, 15
	mtocrf 0b00000100, 16
	mtocrf 0b00000010, 17
	mtocrf 0b00000001, 18

	# swap CRs
	# XXX my hex extraction script can not deal with macros generating more
	# than one instruction
	#crf_xor cr4, cr4, cr5 
	crxor (4*cr4)+0, (4*cr4)+0, (4*cr5)+0
	crxor (4*cr4)+1, (4*cr4)+1, (4*cr5)+1
	crxor (4*cr4)+2, (4*cr4)+2, (4*cr5)+2
	crxor (4*cr4)+3, (4*cr4)+3, (4*cr5)+3
	#crf_xor cr5, cr4, cr5
	crxor (4*cr5)+0, (4*cr4)+0, (4*cr5)+0
	crxor (4*cr5)+1, (4*cr4)+1, (4*cr5)+1
	crxor (4*cr5)+2, (4*cr4)+2, (4*cr5)+2
	crxor (4*cr5)+3, (4*cr4)+3, (4*cr5)+3
	#crf_xor cr4, cr5, cr4
	crxor (4*cr4)+0, (4*cr5)+0, (4*cr4)+0
	crxor (4*cr4)+1, (4*cr5)+1, (4*cr4)+1
	crxor (4*cr4)+2, (4*cr5)+2, (4*cr4)+2
	crxor (4*cr4)+3, (4*cr5)+3, (4*cr4)+3

	#crf_xor cr6, cr6, cr7
	crxor (4*cr6)+0, (4*cr6)+0, (4*cr7)+0
	crxor (4*cr6)+1, (4*cr6)+1, (4*cr7)+1
	crxor (4*cr6)+2, (4*cr6)+2, (4*cr7)+2
	crxor (4*cr6)+3, (4*cr6)+3, (4*cr7)+3
	#crf_xor cr7, cr6, cr7
	crxor (4*cr7)+0, (4*cr6)+0, (4*cr7)+0
	crxor (4*cr7)+1, (4*cr6)+1, (4*cr7)+1
	crxor (4*cr7)+2, (4*cr6)+2, (4*cr7)+2
	crxor (4*cr7)+3, (4*cr6)+3, (4*cr7)+3
	#crf_xor cr6, cr7, cr6
	crxor (4*cr6)+0, (4*cr7)+0, (4*cr6)+0
	crxor (4*cr6)+1, (4*cr7)+1, (4*cr6)+1
	crxor (4*cr6)+2, (4*cr7)+2, (4*cr6)+2
	crxor (4*cr6)+3, (4*cr7)+3, (4*cr6)+3

	# move CR fields to GPRs
	mfocrf 15, 0b00001000
	mfocrf 16, 0b00000100
	mfocrf 17, 0b00000010
	mfocrf 18, 0b00000001

	# align fields in registers for storage
	extrwi 15, 15, 4, 4*4
	extrwi 16, 16, 4, 5*4
	extrwi 17, 17, 4, 6*4
	extrwi 18, 18, 4, 7*4

	# store fields as bytes to memory
	li 5, 7               # init mem pointer to byte 7
	stbu 15, 1(5)
	stbu 16, 1(5)
	stbu 17, 1(5)
	stbu 18, 1(5)
	
	# CR fields at this point
	# cr6 = 0x9 = 0b1001 = {LT, GT, EQ, SO}
	# cr7 = 0x3 = 0b0011 = {LT, GT, EQ, SO}

	# clear cr0 - cr5
	crclr 4*cr0+0
	crclr 4*cr0+1
	crclr 4*cr0+2
	crclr 4*cr0+3
	crclr 4*cr1+0
	crclr 4*cr1+1
	crclr 4*cr1+2
	crclr 4*cr1+3
	crclr 4*cr2+0
	crclr 4*cr2+1
	crclr 4*cr2+2
	crclr 4*cr2+3
	crclr 4*cr3+0
	crclr 4*cr3+1
	crclr 4*cr3+2
	crclr 4*cr3+3
	crclr 4*cr4+0
	crclr 4*cr4+1
	crclr 4*cr4+2
	crclr 4*cr4+3
	crclr 4*cr5+0
	crclr 4*cr5+1
	crclr 4*cr5+2
	crclr 4*cr5+3

	# do some more logical operations
	crand 4*cr0+so, 4*cr6+eq, 4*cr7+lt    # -> 0
	cror 4*cr1+so, 4*cr6+eq, 4*cr7+lt     # -> 0
	crnand 4*cr2+so, 4*cr6+eq, 4*cr7+lt   # -> 1
	crnor 4*cr3+so, 4*cr6+eq, 4*cr7+lt    # -> 1
	crorc 4*cr4+so, 4*cr6+eq, 4*cr7+lt    # -> 1
	crandc 4*cr5+so, 4*cr6+eq, 4*cr7+lt   # -> 0
	creqv 4*cr6+so, 4*cr6+eq, 4*cr7+lt    # -> 1

	# move CR fields to GPRs
	mfocrf 15, 0b10000000
	mfocrf 16, 0b01000000
	mfocrf 17, 0b00100000
	mfocrf 18, 0b00010000
	mfocrf 19, 0b00001000
	mfocrf 20, 0b00000100
	mfocrf 21, 0b00000010

	# align fields in registers for storage
	extrwi 15, 15, 4, 0 
	extrwi 16, 16, 4, 1*4
	extrwi 17, 17, 4, 2*4
	extrwi 18, 18, 4, 3*4
	extrwi 19, 19, 4, 4*4
	extrwi 20, 20, 4, 5*4
	extrwi 21, 21, 4, 6*4
	
	# store fields as bytes to memory
	stb 15, 1(5)
	stb 16, 2(5)
	stb 17, 3(5)
	stb 18, 4(5)
	stb 19, 5(5)
	stb 20, 6(5)
	stbu 21, 7(5)
	

end:
	my_wait


# 
# Result memory pointer in r5
# Pairs to sort in r24 - r31
#
sort_pairs:
	cmplw cr0, 24, 25
	cmplw cr1, 26, 27
	cmplw cr2, 28, 29
	cmplw cr3, 30, 31

	bge cr0, if_25_lt_24
if_24_lt_25:
	stw 24, 0(5)
	stw 25, 4(5)
	b next_0
if_25_lt_24:
	stw 25, 0(5)
	stw 24, 4(5)
next_0:

	bge cr1, if_27_lt_26
if_26_lt_27:
	stw 26, 8(5)
	stw 27, 12(5)
	b next_1
if_27_lt_26:
	stw 27, 8(5)
	stw 26, 12(5)
next_1:

	bge cr2, if_29_lt_28
if_28_lt_29:
	stw 28, 16(5)
	stw 29, 20(5)
	b next_2
if_29_lt_28:
	stw 29, 16(5)
	stw 28, 20(5)
next_2:

	bge cr3, if_31_lt_30
if_30_lt_31:
	stw 30, 24(5)
	stw 31, 28(5)
	b next_3
if_31_lt_30:
	stw 31, 24(5)
	stw 30, 28(5)
next_3:

	blr

	nop
	nop
	nop
