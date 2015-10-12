# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


/** Test logical instructions and the interlocks for interdependent register 
 * accesses
 * */


start:
	addi	3, 0, 0
	addi	4, 0, 0
	ori		3, 0, 0xffff
	ori		4, 0, 0x0001
	li		31, 0

# test simple logic instructions
simple_logic:
	and		5, 3, 4			# r5 = 1
	andc	6, 3, 4			# r6 = 0xfffe
	nand	7, 3, 4			# r7 = 0xfffffffe
	or		8, 3, 4			# r8 = 0xffff
	orc		9, 3, 4			# r9 = 0xffffffff
	nor		10, 3, 4		# r10 = 0xffff0000
	xor		11, 3, 4		# r11 = 0x0000fffe
	eqv		12, 3, 4		# r12 = 0xffff0001
	not		13, 3			# r13 = 0xffff0000

	# Of course, it is slower to use stwu due to interlocks for r31. I just 
	# want to test this instruction.
	stw		5, 0(31)
	stwu	6, 4(31)
	stwu	7, 4(31)
	stwu	8, 4(31)
	stwu	9, 4(31)
	stwu	10, 4(31)
	stwu	11, 4(31)
	stwu	12, 4(31)
	stwu	13, 4(31)

	addi	0, 0, 0
	oris	0, 0, 0xdead
	ori		0, 0, 0xface
	stwu	0, 4(31)

# test complex boolean functions
complex_logic:
	xor		3, 3, 3
	ori		3, 3, 0b10100011	# operand A
	xor		4, 4, 4
	ori		4, 4, 0b10101100	# operand B
	xor		5, 5, 5
	ori		5, 5, 0b11001010	# operand C
	xor		6, 6, 6
	ori		6, 6, 0b00110101	# operand D

	xor		2, 2, 2
	ori		2, 2, 0xaf

	addi	31, 31, 3		# increment mem pointer

/* logic function 0: Y = A !B C !D + A D + B C */
f0:
	andc	16, 3, 4		# term 0
	and		16, 16, 5
	andc	16, 16, 6

	and		17, 3, 6		# term 1

	and		18, 4, 5		# term 2

	or		0, 16, 17
	or		0, 0, 18

	stbu	0, 1(31)

/* logic function 1: Y = A B C D + !A !B !C !D + (A B ^ C D) */
f1:
	and		16, 3, 4
	and		16, 16, 5
	and		16, 16, 6

	not		24, 3
	not		25, 4
	and		17, 24, 25
	not		24, 5
	not		25, 6
	and		17, 17, 24
	and		17, 17, 25

	and		18, 3, 4
	and		19, 5, 6
	xor		20, 18, 19

	or		0, 16, 17
	or		0, 0, 20

	stbu	0, 1(31)

/* logic function 2: y = a ^ b ^ c ^ x ^ c ^ b ^ a (i.e. y = x) 
 *
 * a: r3
 * b: r4
 * c: r5
 * x: r2
 * y: r0
 * */
f2:
	xor 16, 3, 4
	xor 17, 5, 2
	xor 16, 16, 17
	xor 17, 4, 3
	xor 16, 16, 5
	xor 0, 16, 17

	stbu 0, 1(31)	

	.byte 0x7c, 0x00, 0x00, 0x7c         # wait instruction
