# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


/* test conditional branching 
 *
 * calculates 2*5 and stores the result at mem[0]
 *
 * loop counter : r3
 * accumulator  : r5
 *
 * values when encountering the branch instruction:
 *
 * --------------------
 * iteration | r3 | r5
 * ----------+----+----
 * (init)    | -5 |  0
 *      0    | -4 |  2
 *      1    | -3 |  4
 *      2    | -2 |  6
 *      3    | -1 |  8
 *      4    |  0 | 10
 * --------------------
 * */

	addi	3, 0, -5	# set loop counter r3 = -5
	addi	4, 0, 2		# set r4 = 2
	addi	5, 0, 0		# set r5 = 0
	addi	6, 0, 1		# set loop increment r6 = 1

loop:
	add		5, 5, 4		# add r5 = r5 + r4
	add.	3, 3, 6		# increment loop counter
	blta 	loop		# loop if r3 < 0

	stw		5, 0(0)		# store result
	.byte 0x7c, 0x00, 0x00, 0x7c         # wait instruction

