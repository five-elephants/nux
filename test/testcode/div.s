# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


start:
	# load test vectors into registers
	li 15, 9
	li 16, 3
	li 17, 100
	li 18, 2
	li 19, 10
	li 20, 7

    xor 21, 21, 21
	ori 21, 21, 0xffff        # 2^31 -1
	oris 21, 21, 0x7fff
	li 22, 0x0000             # -(2^31)
	oris 22, 22, 0x8000
	xor 23, 23, 23
	ori 23, 23, 0xffff        # -1
	oris 23, 23, 0xffff

	xor 24, 24, 24            # 0

	# apply test vectors and store results to memory
	divw 5, 15, 16
	divw 6, 17, 18
	divw 7, 19, 20
	divw 8, 21, 22

	divw 9, 16, 15 
	divw 10, 18, 17 
	divw 11, 20, 19 
	divw 12, 22, 21 

	stw 5, 0(0)
	stw 6, 1*4(0)
	stw 7, 2*4(0)
	stw 8, 3*4(0)
	stw 9, 4*4(0)
	stw 10, 5*4(0)
	stw 11, 6*4(0)
	stw 12, 7*4(0)

	# repeat with divwu
	divwu 5, 15, 16
	divwu 6, 17, 18
	divwu 7, 19, 20
	divwu 8, 21, 22

	divwu 9, 16, 15 
	divwu 10, 18, 17 
	divwu 11, 20, 19 
	divwu 12, 22, 21 

	stw 5, 8*4(0)
	stw 6, 9*4(0)
	stw 7, 10*4(0)
	stw 8, 11*4(0)
	stw 9, 12*4(0)
	stw 10, 13*4(0)
	stw 11, 14*4(0)
	stw 12, 15*4(0)

	# test corner cases: division by zero and -2^31 / -1
	li 2, 16*4           # prepare result mem pointer
	divwo. 5, 15, 24     # division by zero
	bsol div_over

	addi 2, 2, 4
	divwo. 5, 24, 24
	bsol div_over

	addi 2, 2, 4
	divwo. 5, 24, 16     # division 0 / 3
	stw 5, 0(2)
	bsol div_over

	# calculate remainder

	# remainder of 10 / 7 == 3
	mr 3, 19
	mr 4, 20
	bl calc_rem
	stw 2, 19*4(0)

	# remainder of 100 / 3 == 1
	mr 3, 17
	mr 4, 16
	bl calc_rem
	stw 2, 20*4(0)
	
	# test setting of condition register fields
	divw. 5, 17, 18           # 100 / 2 == 50
	beq skip_st_0
	stw 5, 21*4(0)
skip_st_0:
	divw. 5, 18, 17           # 2 / 100 == 0
	beq skip_st_1
	stw 5, 22*4(0)
	b end

skip_st_1:
	li 5, 0x1111
	stw 5, 22*4(0)

end:
	.byte 0x7c, 0x00, 0x00, 0x7c

# function to mark division overflow
div_over:
	xor 3, 3, 3
	mtxer 3
	ori 3, 3, 0xdead
	stw 3, 0(2)
	blr

# function to calculate the remainder of r3/r4 and place it in r2
calc_rem:
	divw 2, 3, 4
	mullw 2, 2, 4
	subf 2, 2, 3
	blr

	nop
	nop
	nop
