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
	li 0, 0x0ff0   # data
	li 1, 0        # address base
	li 2, 0        # address offset
	li 31, 4       # set shift range
	ecowx 0, 1, 2
	eciwx 3, 1, 2
	stw 3, 0(0)
	
	li 0, 0x0ee0
	ecowx 0, 1, 2
	eciwx 3, 1, 2
	stw 3, 4(0)

	xor 4, 4, 4
	xor 6, 6, 6
	ori 6, 6, 0xface
	oris 6, 6, 0xdead

w_loop:
	ecowx 6, 1, 4  # write to DEV[r1 + r4]
	rotlw 6, 6, 31  # rotate left by 4 
	addi 4, 4, 4   # increment loop counter by 4
	cmpi 0, 4, 128 
	blt w_loop     # branch if loop counter < 100

	xor 4, 4, 4

	li 2, 0x10 
r_loop:
	eciwx 7, 1, 4  # read from DEV[r1 + r4]
	stwx 7, 2, 4   # write to MEM[r1 + r4]
	addi 4, 4, 4   # increment loop counter by 4
	cmpi 0, 4, 128
	blt r_loop     # branch if loop counter < 100

	.byte 0x7c, 0x00, 0x00, 0x7c
