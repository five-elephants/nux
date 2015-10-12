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
	xor 1, 1, 1         # clear r1
	lwz  0, 0(1)        # load mem[0:3]
	lwzu 2, 4(1)        # load mem[4:7]
	lwzu 3, 4(1)        # load mem[8:11]
	lwzu 4, 4(1)        # ...
	lwzu 5, 4(1)
	lwzu 6, 4(1)
	lwzu 7, 4(1)
	lwzu 8, 4(1)
	lwzu 9, 4(1)
	lwzu 10, 4(1)
	lwzu 11, 4(1)
	lwzu 12, 4(1)
	lwzu 13, 4(1)
	lwzu 14, 4(1)
	lwzu 15, 4(1)
	lwzu 16, 4(1)
	lwzu 17, 4(1)
	lwzu 18, 4(1)
	lwzu 19, 4(1)
	lwzu 20, 4(1)
	lwzu 21, 4(1)
	lwzu 22, 4(1)
	lwzu 23, 4(1)
	lwzu 24, 4(1)
	lwzu 25, 4(1)
	lwzu 26, 4(1)
	lwzu 27, 4(1)
	lwzu 28, 4(1)
	lwzu 29, 4(1)
	lwzu 30, 4(1)
	lwzu 31, 4(1)       # load mem[124:127]

	stwu 0, 8(1)        # store mem[132:135] = r1
	stwu 2, 4(1)        # store mem[136:139] = r2
	stwu 3, 4(1)        # ...
	stwu 4, 4(1)
	stwu 5, 4(1)
	stwu 6, 4(1)
	stwu 7, 4(1)
	stwu 8, 4(1)
	stwu 9, 4(1)
	stwu 10, 4(1)
	stwu 11, 4(1)
	stwu 12, 4(1)
	stwu 13, 4(1)
	stwu 14, 4(1)
	stwu 15, 4(1)
	stwu 16, 4(1)
	stwu 17, 4(1)
	stwu 18, 4(1)
	stwu 19, 4(1)
	stwu 20, 4(1)
	stwu 21, 4(1)
	stwu 22, 4(1)
	stwu 23, 4(1)
	stwu 24, 4(1)
	stwu 25, 4(1)
	stwu 26, 4(1)
	stwu 27, 4(1)
	stwu 28, 4(1)
	stwu 29, 4(1)
	stwu 30, 4(1)
	stwu 31, 4(1)       # store mem[232:235] = r31

	addi 1, 1, 4
	li 2, -1            # set load pointer
	li 0, -1            # set loop increment
	li 3, 2             # set loop iteration count
	li 5, 1             # set load address increment
copy_loop:
	lbzux 16, 2, 5      # load one word in bytes
	lbzux 17, 2, 5
	lbzux 18, 2, 5
	lbzux 19, 2, 5

	stbu 19, 4(1)        # store in reversed byte-order
	stb 18, 1(1)
	stb 17, 2(1)
	stb 16, 3(1)

	add. 3, 3, 0        # decrement loop counter r3
	bne copy_loop       # branch loop


end:
	.byte 0x7c, 0x00, 0x00, 0x7c

	nop
	nop
	nop

