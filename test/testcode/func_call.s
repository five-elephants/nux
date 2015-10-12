# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


/**
 * Test program to test/demonstrate function calls
 * */

start:
	li 2, 1023*4   # stackpointer
	li 3, 10
	li 4, 12
	bl f0
	stw 3, 0(0)

	li 16, 0x11
	li 17, 0x22
	li 18, 0x33
	li 19, 0x44

	li 3, 1
	li 4, 2
	li 5, 4
	li 6, 4
	bl store_shifted

	xor 3, 3, 3
	ori 3, 3, 0xface
	oris 3, 3, 0xdead
	li 4, 4
	li 5, 24
	li 6, 8
	bl store_shifted

	li 3, 11
	li 4, 3
	bl mult
	stw 3, 15*4(0)


	li 3, 27
	li 4, 82
	bl mult
	stw 3, 16*4(0)

	xor 3, 3, 3
	xor 4, 4, 4
	xor 5, 5, 5
	xor 6, 6, 6
	ori 3, 3, 0x5678
	oris 3, 3, 0x1234
	mr 4, 3
	ori 5, 5, 0x4321
	oris 5, 5, 0x8765
	mr 6, 5
	bl add64
	stw 7, 17*4(0)
	stw 8, 18*4(0)

	xor 3, 3, 3
	xor 4, 4, 4
	xor 5, 5, 5
	xor 6, 6, 6
	ori 3, 3, 0xffff
	oris 3, 3, 0x0000
	ori 4, 4, 0xffff
	oris 4, 4, 0xffff
	li 6, 1
	bl add64
	stw 7, 19*4(0)
	stw 8, 20*4(0)

	b end

/* function f0: addr r3 + r4 and place the result in r3 */
f0:
	add 3, 3, 4
	blr

/* function store_shifted: store r3 rotated left by r4 at address r5. 
 * repeat r6 times */
store_shifted:
	stw 16, 0(2)
	stw 17, -4(2)
	stw 18, -8(2)
	addi 2, 2, -12		# update stackpointer
	
	mr 16, 3
	mr 17, 5			# init mem pointer
	xor 18, 18, 18		# init loop counter

	stw 3, 0(17)		# store initial value

store_shifted_loop:
	rotlw 16, 16, 4		# rotate
	stwu 16, 4(17)		# store
	addi 18, 18, 1		# increment loop counter
	cmpw 18, 6			# loop condition
	blt store_shifted_loop

	lwz 18, 4(2)
	lwz 17, 8(2)
	lwzu 16, 12(2)
	blr


/* software multiplication function.
 * Place arguments in r3, r4. get result from r3 */
mult:
	stw 16, 0(2)
	stw 17, -4(2)
	stw 18, -8(2)
	stw 19, -12(2)
	addi 2, 2, -16		# update stackpointer

	xor 19, 19, 19
	mr 16, 3
	mr 17, 4
	xor 18, 18, 18

mult_loop:
	andi. 19, 16, 1		# is r16 odd?
	beq mult_skip_add
	add 18, 18, 17		# accumulate result if not even
mult_skip_add:
	slwi 17, 17, 1
	srwi. 16, 16, 1
	bne mult_loop
	
	mr 3, 18

	lwz 19, 4(2)
	lwz 18, 8(2)
	lwz 17, 12(2)
	lwzu 16, 16(2)
	blr


/* extended 64-bit add 
 * Place arguments in r3, r4 and r5, r6
 * Get result from r7, r8
 * */
add64:
	addc 8, 4, 6
	adde 7, 3, 5
	blr

/* multiply using booth algorithm
 * (r5, r6) = r3 * r4 */
##mult_booth:
##	stw 16, 0(2)
##	stw 17, 4(2)
##	addi 2, 2, -8
##
##	# A = ( r3 , 0  )
##	# S = ( r16, 0  )   r16 = -r3
##	# P = ( 0  , r4 )
##	neg 16, 3				# init values
##	mr 6, 4
##	xor 5, 5, 5
##	li 17, 1
##	
##1:	andi. 18, 4, 17			# is the lsb set?
##	
##
##	lwz 17, 4(2)
##	lwzu 16, 8(2)
##	blr

end:
	stb 16, 4*1023(0)
	stb 17, 4*1023+1(0)
	stb 18, 4*1023+2(0)
	stb 19, 4*1023+3(0)

	.byte 0x7c, 0x00, 0x00, 0x7c         # wait instruction
