# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


#  000000b8 <ee_vsprintf>:
# b8:       38 00 01 00     li      r0,256
# bc:       39 20 00 00     li      r9,0
# c0:       7c 09 03 a6     mtctr   r0
# c4:       7c 04 48 ae     lbzx    r0,r4,r9
# c8:       7c 03 49 ae     stbx    r0,r3,r9
# cc:       39 29 00 01     addi    r9,r9,1
# d0:       42 00 ff f4     bdnz+   c4 <ee_vsprintf+0xc>
# d4:       38 60 01 00     li      r3,256
# d8:       4e 80 00 20     blr


start:
	li 4, 0
	li 3, 256
	bl ee_vsprintf

end:
	.byte 0x7c, 0x00, 0x00, 0x7c


# Copies 256 bytes from location in r4 to location in r3.
# Returns number of bytes copied.
ee_vsprintf:
	li 0, 256
	li 9, 0
	mtctr 0
loop:
	lbzx 0, 4, 9
	stbx 0, 3, 9
	addi 9, 9, 1
	bdnz loop
	li 3, 256
	blr

