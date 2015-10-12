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

nvemtl 0, 16, 17
nvemtl 1, 18, 19

li 0, 0x1111
nvem 1, 0, 0
nvem 2, 0, 1
stw 1, 0(0)
stw 2, 4(0)

lis 0, 0x0123
ori 0, 0, 0x4567
nvem 1, 0, 0
nvem 2, 0, 1
stw 1, 8(0)
stw 2, 12(0)


# now test compare and select

lis 3, 0xab00
ori 3, 3, 0x00ba
nvecmpi 0, 3, 0xa
nves 4, 0, 1
nvecmpi 0, 3, 0xb
nves 5, 4, 2
stw 4, 16(0)
stw 5, 20(0)

wait
