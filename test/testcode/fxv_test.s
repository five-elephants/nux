# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


.section .text
	#li 0, res@l
	#li 1, opa@l
	#li 2, opb@l
	#li 4, res2@l
	li 0, 0
	li 1, NUM_SLICES * 0x10
	li 2, NUM_SLICES * 0x10 + NUM_SLICES * 0x10
	li 4, 2 * NUM_SLICES * 0x10 + NUM_SLICES * 0x10
	li 3, NUM_SLICES*8*2

	fxvlax 1, 0, 0
	fxvlax 2, 0, 1
	fxvmahm 0, 1, 2      # ACC <- 1 * 2 [ACC <- 6]
	fxvstax 0, 0, 2

test2:
	fxvsubhm 0, 2, 1
	fxvstax 0, 0, 4

perf_test:
loop:
	fxvmahm 4, 1, 1   # 4 <- 1 * 1 + ACC [ACC <- 10, 14, 18, ..., 
	                  # 10 + 4*32]
	fxvmahm 5, 1, 1
	fxvmahm 6, 1, 1
	fxvmahm 7, 1, 1
	fxvmahm 8, 1, 1
	fxvmahm 9, 1, 1
	fxvmahm 10, 1, 1
	fxvmahm 11, 1, 1
	fxvmahm 12, 1, 1
	fxvmahm 13, 1, 1
	fxvmahm 14, 1, 1
	fxvmahm 15, 1, 1
	fxvmahm 16, 1, 1
	fxvmahm 17, 1, 1
	fxvmahm 18, 1, 1
	fxvmahm 19, 1, 1
	fxvmahm 20, 1, 1
	fxvmahm 21, 1, 1
	fxvmahm 22, 1, 1
	fxvmahm 23, 1, 1
	fxvmahm 24, 1, 1
	fxvmahm 25, 1, 1
	fxvmahm 26, 1, 1
	fxvmahm 27, 1, 1
	fxvmahm 28, 1, 1
	fxvmahm 29, 1, 1
	fxvmahm 30, 1, 1
	fxvmahm 31, 1, 1

	subic. 3, 3, 1
	bne loop	

	wait

.section .data
	opa: .fill NUM_SLICES*8, 2, 0x0002
	opb: .fill NUM_SLICES*8, 2, 0x0003
.ifdef RESULT
	res: .fill NUM_SLICES*8, 2, 0x0006
	res2: .fill NUM_SLICES*8, 2, 0x0001
.else
	res: .skip NUM_SLICES*8*2
	res2: .fill NUM_SLICES*8, 2, 0x0000
.endif	
