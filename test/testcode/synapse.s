# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.



lis 16, 0x1234
ori 16, 16, 0x5678
lis 17, 0x9abc
ori 17, 17, 0xdeff

lis 18, 0x0012
ori 18, 18, 0x3456
lis 19, 0x789a
ori 19, 19, 0xbcde

synmtl 0, 16, 17
synmtl 1, 18, 19

li 20, 0x123
li 21, 0x456
li 22, 0x789
li 23, 0xabc
synmtvr 0, 20, 0
synmtvr 0, 21, 1
synmtvr 0, 22, 2
synmtvr 0, 23, 3

synm 1, 0, 0
synm 2, 0, 1
synmvvr 3, 0
syncmpi 3, 0xf0
syns 3, 2, 1

li 3, 0
bl store_vrs

synswp

synmtvr 0, 20, 0
synmtvr 0, 21, 1
synmtvr 0, 22, 2
synmtvr 0, 23, 3

synm 2, 0, 0
synm 1, 0, 1
synmvvr 3, 0
syncmpi 3, 0xf0
syns 3, 2, 1

li 3, 16
bl store_vrs


lis 0, 0x1350
li 1, 0
li 2, 0
synops 0, 1, 2
addi 2, 2, 4
li 3, 32
synswp
synops 0, 1, 2
bl store_vrs

lis 1, 0x1
li 2, 0x0
synops 0, 1, 2

syncmpi. 1, 0xf1

wait


store_vrs:
	synmfvr 4, 0, 0
	synmfvr 5, 0, 1
	synmfvr 6, 0, 2
	synmfvr 7, 0, 3

	stw 4, 0(3)
	stw 5, 4(3)
	stw 6, 8(3)
	stw 7, 12(3)

	blr
