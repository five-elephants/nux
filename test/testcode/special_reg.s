# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


/*
 * Program to test instructions using special purpose registers
 * */

start:
	/* Test data hazard mtxer to adde */
	xor 0, 0, 0
	li 1, 0xf
	li 2, 0x1
	oris 0, 0, 0x2000
	mtxer 0
	adde 3, 1, 2
	stw 3, 0(0)

	/* Test read/write CTR */
	mtctr 1
	mfctr 4
	stw 4, 4(0)

	/* Test read/write LNK */
	slwi 1, 1, 4
	mtlr 1
	mflr 4
	stw 4, 8(0)

	/* Test read/write CR */
	xor 4, 4, 4
	li 0, 0xf
	slwi 0, 0, 28
	mtocrf 0b10000000, 0
	mfocrf 4, 0b10000000   
	stw 4, 12(0)

	/* Test data hazard write CR -> branch conditional */
	li 0, 0x2		# set zero bit in CR0
	slwi 0, 0, 24
	mtocrf 0b01000000, 0
	beq cr1, skip
	stw 2, 16(0)
skip:
	
#	/* Test data hazard write CTR -> branch to CTR */
#	li 2, -1
#	li 0, skip2
#	mtctr 0
#	bctr
#	stw 2, 20(0)
#
#skip2:
#	li 2, 1
#	stw 2, 20(0)

	.byte 0x7c, 0x00, 0x00, 0x7c         # wait instruction
