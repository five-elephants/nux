# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


reset:
	b start

	# interrupt jump table
	int_mcheck:    b isr_undefined
	int_cinput:    b isr_undefined
	int_dstorage:  b isr_undefined
	int_istorage:  b isr_undefined
	int_einput:    b isr_einput
	int_alignment: b isr_undefined
	int_program:   b isr_undefined
	int_syscall:   b isr_undefined
	int_doorbell:  b isr_undefined
	int_cdoorbell: b isr_undefined

start:
	# init interrupt counters
	xor 0, 0, 0
	stw 0, 0(0)

	#
	# output a bit sequence on the pins
	#

	# initialization
	li 15, 0xf               # r15 = 0xf
	li 16, 10                # r16 = 10
	li 28, 0x1               # r28 = 0x1  output pattern 0
	li 29, 0x2               # r29 = 0x2  output pattern 1
	li 30, 0x4               # r30 = 0x4  output pattern 2
	li 31, 0x8               # r31 = 0x8  output pattern 3

	# enable output driver for all four pins
	mtspr 0b0001000011, 15   # GOE = r15 

	mtctr 16                 # CTR = r16
	# output current pattern
	mtspr 0b0001000010, 28   # GOUT = r28
out_loop:
	bdnz out_loop            # branch if CTR != 0 and CTR--

	mtctr 16                 # reload CTR = r16
	mtspr 0b0001000010, 29   # GOUT = r29
out_loop_1:
	bdnz out_loop_1          # branch if CTR != 0 and CTR--

	mtctr 16                 # reload CTR = r16
	mtspr 0b0001000010, 30   # GOUT = r30
out_loop_2:
	bdnz out_loop_2          # branch if CTR != 0 and CTR--

	mtctr 16                 # reload CTR = r16
	mtspr 0b0001000010, 31   # GOUT = r31
out_loop_3:
	bdnz out_loop_3          # branch if CTR != 0 and CTR--


	# 
	# read a pattern from the pins and store them in memory
	#
	
	# set all pins to input
	li 15, 0x0
	li 17, 0                 # set mem pointer r17 = 4
	mtspr 0b0001000011, 15   # set GOE = 0xf

	mfspr 19, 0b0001000001   # load r19 from GIN register as compare value

	# sample loop: read pins until change detected
in_loop:
	mfspr 18, 0b0001000001   # load r18 from GIN register
	cmpw 18, 19
	beq in_loop
	
	# store sampled value to memory
	stwu 18, 4(17)
	mr 19, 18                # update compare register for change detection

	# repeat until mem pointer r17 == 16
	cmpwi 17, 16
	bne in_loop
	
	# delay program for some time
	li 16, 20
	mtctr 16
delay_loop:
	nop
	bdnz delay_loop

	#
	# set pin 0 to input and configure interrupt to trigger on high level
	#
	xor 15, 15, 15
	li 15, 0xe
	lis 16, 0x000f
	ori 16, 16, 0x0100
	mtspr 0b0001000011, 15   # set GOE = 0xe
	mtspr 0b0001000100, 16   # set ICCR.gin_sense_level = 0xf
	                         #     ICCR.gin_trigger = 0x0
							 #     ICCR.gin_mask = 0x1
							 #     ICCR.doorbell_en = 0
	mfmsr 17
	ori 17, 17, 0x8000
	mtmsr 17                 # enable external interrupt sources

wait_loop:
	lwz 18, 0(0)             # load pin interrupt counter to r18
	cmpwi 18, 0              # compare r18 to zero
	beq wait_loop            # branch if pin interrupt counter == 0

	# re-enable external interrupt sources
	mfmsr 19
	ori 19, 19, 0x8000
	mtmsr 19

	# test instruction sequence mtmsr, wait
	.byte 0x7c, 0x00, 0x00, 0x7c # wait instruction

	# change to edge triggered interrupts
	lis 16, 0x0000
	ori 16, 16, 0x0100
	mtspr 0b0001000100, 16

isr_undefined:
	.byte 0x7c, 0x00, 0x00, 0x7c # wait instruction
	b isr_undefined


#
# External input ISR
#
# Counts the number of interrupts in mem[0]. For the first interrupt external
# interrupt sources are disabled.
#
isr_einput:
	lwz 1, 0(0)
	cmpwi 1, 0
	addi 1, 1, 1
	stw 1, 0(0)
	bne isr_einput_out
	mfsrr1 1
	andi. 1, 1, 0x7fff
	mtsrr1 1                 # disable external interrupt sources

isr_einput_out:
	rfi

	nop
	nop
	nop
