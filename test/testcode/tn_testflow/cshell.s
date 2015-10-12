# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http:#solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


/*
 * This program runs all the programs generated with the C-compiler
 *
 * The stack pointer r1 is initially set to zero. A value of 0xffc seems to
 * conflict with the C-ABI. I have to check that.
 * */

.extern start 

#.section system, "ax", @progbits
.text
.extern _start:
reset:
	#xor 1, 1, 1   # init stack pointer
	li 1, 0x7ff8
	#ori 1, 1, 0x4000
	#addi 1, 1, -8
	
	bl start

end_loop:
	.byte 0x7c, 0x00, 0x00, 0x7c         # wait instruction
	b end_loop


#.data
#hello: .ascii "Hello World from my own Processor\0"
