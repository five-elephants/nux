# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.



.macro my_wait
	.byte 0x7c, 0x00, 0x00, 0x7c
.endm

.macro my_popcntb ra, rs
	.hword (31 << 10) | (\rs << 5) | \ra, (122 << 1)
.endm

.macro my_prtyw ra, rs
	.hword (31 << 10) | (\rs << 5) | \ra, (154 << 1)
.endm
