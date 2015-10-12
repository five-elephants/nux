# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


/* Test interlocks with various operations */

	lwz		3, 0(0)		# load operands
	lwz		4, 4(0)
	add		5, 3, 4		# interdependend add instructions
	add		6, 4, 5
	add		7, 5, 6
	
	addi	31, 0, 16*4	# set r31 = 16

	stw		5, 0(31)	# store results of adds beginning at address 16
	stw		6, 4(31)
    stw		7, 8(31)


    addi	3, 0, 1		# set r3 = 1
	addi	4, 0, 0		# set r4 = 0
	add		4, 4, 3		# increment r4 by r3
	add		4, 4, 3
	add		4, 4, 3
	add 	4, 4, 3
	stw		4, 12(31)	# store result

	addi	3, 0, 1		# set r3 = 1
	add		3, 3, 3		# r3 = r3 + r3
	add		3, 3, 3		
	add		3, 3, 3
	stw		3, 16(31)	# store result

	.byte 0x7c, 0x00, 0x00, 0x7c         # wait instruction
