# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


###############################################################################
# 65_doorbell
#
# Test triggering the doorbell interrupt from JTAG.
# Counts the number of occurences and stores the number in mem[0].
# Also looks at mem[1] and if not zero stores the value in mem[r3++].
###############################################################################

reset:
	b start

	# interrupt jump table
	int_mcheck:    b isr_undefined
	int_cinput:    b isr_undefined
	int_dstorage:  b isr_undefined
	int_istorage:  b isr_undefined
	int_einput:    b isr_undefined
	int_alignment: b isr_undefined
	int_program:   b isr_undefined
	int_syscall:   b isr_undefined
	int_doorbell:  b isr_doorbell
	int_cdoorbell: b isr_undefined

start:
	# zero the mem store pointer
	xor 3, 3, 3
	
	# zero the doorbell interrupt counter
	xor 15, 15, 15 
	stw 15, 0(0)

	# enable the doorbell interrupt
	lis 16, 0x0000
	ori 16, 16, 0x0001
	mtspr 0b0001000100, 16   # set ICCR.gin_sense_level = 0x0
	                         #     ICCR.gin_trigger = 0x0
							 #     ICCR.gin_mask = 0x0
							 #     ICCR.doorbell_en = 1

	mfmsr 17
	ori 17, 17, 0x8000
	mtmsr 17                 # enable external interrupt sources

isr_undefined:
	.byte 0x7c, 0x00, 0x00, 0x7c # wait instruction
	b isr_undefined


isr_doorbell:
	lwz 1, 0(0)              # load interrupt counter
	lwz 2, 32*4(0)           # load mailbox
	addi 1, 1, 1
	cmpwi 2, 0               # only store mailbox if != 0
	beq isr_doorbell_out

	# store the mailbox value into memory pointed at by r3
	stwu 2, 4(3)

isr_doorbell_out:
	stw 1, 0(0)              # store interrupt counter
	rfi

	nop
	nop
	nop
