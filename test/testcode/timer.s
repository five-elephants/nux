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
# 65_timer
#
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
	int_doorbell:  b isr_undefined
	int_cdoorbell: b isr_undefined
	int_fit:       b isr_fit
	int_dec:       b isr_dec

start:
	li 4, -4
	li 5, 64                    # set decrementer interval register r5 to 64
	li 15, 100
	li 18, 0
	xor 19, 19, 19
	xor 20, 20, 20
	mtctr 15
	stw 18, 32*4(0)
	stw 18, 33*4(0)
	stw 18, 34*4(0)

ref_loop:
	nop
	bdnz ref_loop

	mfspr 16, 285                # read TBU
	mfspr 17, 284                # read TBL

	mtspr 285, 19                # load TBU
	mtspr 284, 20                # load TBL

	stw 16, 4(4)                 # store TBU
	stwu 17, 8(4)                # store TBL and increment mem pointer

	# loop again if r18 == 0
	cmpwi 18, 2 
	mtctr 15
	addi 18, 18, 1
	blt ref_loop

	#
	# Test decrementer
	#
	
	# react to TSR.DIS
	mtdec 15                     # load DEC = r15 (== 100)
	li 17, 0x1111                # load magic number for later use
	lis 18, 0x0800               # set TSR.DIS bit mask
	lis 19, 0xffff               # set clear-all mask

dec_wait_loop:
	mfspr 16, 336                # get the TSR
	and 16, 16, 18               # mask to get only TSR.DIS
	cmpwi 16, 0                  # is bit set?
	beq dec_wait_loop            # loop until bit is set
	
	stw 17, 34*4(0)              # store magic number to mark occurence of TSR.DIS
	mtspr 336, 19                # clear all TSR bits

	# now use an interrupt
	lis 18, 0x0400               # set TCR value with TCR.DIE = 1
	mtspr 340, 18                # set TCR (enable decrementer interrupt)

	mfmsr 17
	ori 17, 17, 0x8000
	mtmsr 17                     # enable external interrupt sources

	mtdec 15                     # load DEC = r15 (== 100)

isr_undefined:
	.byte 0x7c, 0x00, 0x00, 0x7c # wait instruction
	b isr_undefined

isr_fit:
	lwz 1, 33*4(0)
	lis 2, 0x0400                # set TSR clear-all mask
	addi 1, 1, 1
	stw 1, 33*4(0)
	mtspr 336, 2                 # clear all TSR bits
	rfi

isr_dec:
	lwz 1, 32*4(0)
	lis 2, 0x0800                # set TSR clear DIS mask
	cmpwi 1, 3                   # compare interrupt counter value to 4
	addi 1, 1, 1
	stw 1, 32*4(0)
	blt isr_dec_out              # don't clear if interrupt counter < 4

	mtspr 336, 2                 # clear all TSR bits

	# check wheter in auto-reload mode
	mfspr 2, 340                 # get TCR
	andis. 2, 2, 0x0040          # check ARE bit
	bne isr_dec_out              # return from ISR if set

	# set new decrementer value and divide the current value by two to make
	# ever smaller intervals between interrupts
	mtdec 5
	srwi. 5, 5, 1
	
	# disable decrementer interrupt when interval reaches zero
	bne isr_dec_out
	lis 1, 0x04c0                # set TCR update value with DIE = 1, FIE = 1 and ARE = 1
	li 2, 550                    # set DECAR value to 512
	mtspr 54, 2                  # load DECAR
	mtdec 2                      # load DEC
	mtspr 340, 1                 # load TCR

isr_dec_out:
	rfi

	nop
	nop
	nop
