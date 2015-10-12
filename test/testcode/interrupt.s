# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


# Test some interrupts

# this must be at address 0
reset:
	b start

	# interrupt jump table
	int_mcheck:    b isr_undefined
	int_cinput:    b isr_undefined
	int_dstorage:  b isr_undefined
	int_istorage:  b isr_undefined
	int_einput:    b isr_undefined
	int_alignment: b isr_alignment
	int_program:   b isr_program
	int_syscall:   b isr_undefined
	int_doorbell:  b isr_undefined
	int_cdoorbell: b isr_undefined

start:
	xor 31, 31, 31  # zero r31
	stw 31, 0(0)    # init alignment interrupt counter
	stw 31, 4(0)    # init program interrupt counter

	lwz 3, 5(0)  # cause alignment exception

	addi 1, 1, 1
	lwz 4, 7(1)  # should not cause an exception
	li 4, 0      # get rid of undefined contents in r4


	li 5, 10     # r5 = 10
	twgti 5, 7   # trap if r5 > 7
	# r5 == 7 after 3 interrupts

	li 6, 10     # r6 = 10
	twgt 5, 6    # trap if r5 > r6
	# r5 == 7 no interrupt
	
	li 6, 5      # r6 = 5
	twgt 5, 6    # trap if r5 > r6
	# r5 == 5 after 2 interrupts

	tweq 5, 6    # trap if r5 == r6
	# r5 == 4 after 1 interrupt

	li 10, 0x1111
	mfmsr 10

	li 10, 0x0aff
	mtmsr 10
end:
	.byte 0x7c, 0x00, 0x00, 0x7c   # halt processor

#------------------------------------------------------------------------------
isr_alignment:
	lwz 31, 0(0)       # load alignment exception counter
	addi 31, 31, 1     # increment counter
	stw 31, 0(0)       # store new value
	mfsrr0 31          # get interrupt return address
	addi 31, 31, 4     # increment return address to point to following instruction
	mtsrr0 31          # store new return address
#	nop                # hack: no hazard detection for SRR0 at the moment
#	nop
#	nop
	rfi	
	
isr_program:
	lwz 31, 4(0)       # load program exception counter
	addi 31, 31, 1     # increment counter
	stw 31, 4(0)       # store new value

	subi 5, 5, 1       # decrement r5
	rfi

isr_undefined:
	.byte 0x7c, 0x00, 0x00, 0x7c   # halt processor

	nop
	nop
	nop
