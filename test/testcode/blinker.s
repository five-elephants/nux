# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


/* LED blinker program primarily for the FPGA implementation */

start:
	xor 0, 0, 0
	xor 1, 1, 1

loop:
	srwi 0, 1, 24
	#srwi 0, 1, 4
	mtspr 0b0001000010, 0
	addi 1, 1, 1
	b loop


