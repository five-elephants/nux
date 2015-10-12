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
	li 2, 0

	# multiply 2 * 3 and store the complete 64bit result
	li 16, 2
	li 17, 3
	mulhw 0, 16, 17
	mullw 1, 16, 17
	stw 0, 0(2)
	stwu 1, 4(2)

	# multiply 2 * -3 and store the complete 64bit result
	li 16, 2
	li 17, -3
	mulhw 0, 16, 17
	mullw 1, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)
	mulhwu 0, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)
	
	# multiply -1 * -1 and store the complete 64bit result
	li 16, -1
	li 17, -1
	mulhw 0, 16, 17
	mullw 1, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)

	# multiply 2^31-1 * 2^31-1 and store the complete 64bit result
	xor 16, 16, 16
	ori 16, 16, 0xffff
	oris 16, 16, 0x7fff
	mr 17, 16
	mulhw 0, 16, 17
	mullw 1, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)
	mulhwu 0, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)

	# multiply -(2^31-1) * 2^31-1 and store the complete 64bit result
	neg 16, 16
	mulhw 0, 16, 17
	mullw 1, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)
	mulhwu 0, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)

	# multiply -(2^31-1) * -(2^31-1)
	neg 17, 17
	mulhw 0, 16, 17
	mullw 1, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)
	mulhwu 0, 16, 17
	stw 0, 4(2)
	stwu 1, 8(2)


	# test multiply in sequences with different arguments
	li 18, 5
	li 19, 10
	mulhw 28, 16, 17
	mullw 31, 18, 19
	mullw 29, 16, 17
	mulhw 30, 18, 19

	stmw 28, 4(2)
#	stw 28, 4(2)
#	stw 29, 8(2)
#	stw 30, 12(2)
#	stw 31, 16(2)
	addi 2, 2, 16


	# test multiply with immediate
	xor 30, 30, 30
	mulli 31, 19, 8
	stw 30, 4(2)
	stwu 31, 8(2)

end:
	.byte 0x7c, 0x00, 0x00, 0x7c

	nop
	nop
	nop
