# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


/* Test wether inerlocks are correctly working */

start:
	lwz		3, 0(0)		# load two operands from memory
	lwz		4, 4(0)
	add		5, 3, 4		# add them
	stw		5, 8(0)		# store the result in memory
	ba		do_this		# jump down

dont_do_this:
	addi	3, 0, 10	# set r3 = 10
	addi	4, 0, 20	# set r4 = 20

do_this:
	add		6, 3, 4		# add r3 and r4
	stw		6, 12(0)	# store the result in memory


	addi	6, 0, 0xfe	# set r6 to mem-pattern 0xfe
	addi	3, 0, 10	# set r3 = 10
	addi	4, 0, -1	# set r4 = -1
loop:
	add.	3, 4, 3		# subtract 1 from r3
	bnea	loop
	
	stw		6, 32(0)
	.byte 0x7c, 0x00, 0x00, 0x7c         # wait instruction
