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
	li 15, 1
	li 16, 2
	li 17, 3
	li 18, 4
	li 19, 5
	li 20, 6
	li 21, 7
	li 22, 8
	li 23, 9
	li 24, 10

	lis 12, 0xc000
	li 13, 0x0000


	# test word-sized read/write access to IO address space
	stw 15, 0(12)
	stw 16, 4(12)
	stw 17, 8(12)
	stw 18, 12(12)

	lwz 0, 0(12)
	stw 0, 0(13)
	lwz 0, 4(12)
	stw 0, 4(13)
	lwz 0, 8(12)
	stw 0, 8(13)
	lwz 0, 12(12)
	stw 0, 12(13)
	
	# test the same using load/store with update instructions
	stwu 15, 16(12)
	stwu 16, 4(12)
	stwu 17, 4(12)
	stwu 18, 4(12)

	lwzu 0, -12(12)
	stwu 0, 16(13)

	lwzu 0, 4(12)
	stwu 0, 4(13)

	lwzu 0, 4(12)
	stwu 0, 4(13)

	lwzu 0, 4(12)
	stwu 0, 4(13)
	
	# test load/store indexed instructions
	lis 12, 0xc000
	addi 12, 12, 8*4
	li 13, 8*4
	li 14, 0

	stwx 19, 12, 14
	addi 14, 14, 4
	stwx 20, 12, 14
	addi 14, 14, 4
	stwx 21, 12, 14
	addi 14, 14, 4
	stwx 22, 12, 14

	li 14, 0

	lwzx 0, 12, 14
	stwx 0, 13, 14
	addi 14, 14, 4
	lwzx 0, 12, 14
	stwx 0, 13, 14
	addi 14, 14, 4
	lwzx 0, 12, 14
	stwx 0, 13, 14
	addi 14, 14, 4
	lwzx 0, 12, 14
	stwx 0, 13, 14
	addi 14, 14, 4

	# test load/store indexed with update
	# test load/store multiple
end:
	.byte 0x7c, 0x00, 0x00, 0x7c
