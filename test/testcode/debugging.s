# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


.include "macros.s"

reset:
	b start

	# interrupt jump table
	int_mcheck:    b isr_undefined
	int_cinput:    b isr_undefined
	int_dstorage:  b isr_undefined
	int_istorage:  b isr_undefined
	int_einput:    b isr_undefined
	int_alignment: b isr_undefined
	int_program:   b isr_program
	int_syscall:   b isr_undefined
	int_doorbell:  b isr_undefined
	int_cdoorbell: b isr_undefined
	int_fit:       b isr_undefined
	int_dec:       b isr_undefined

start:
  li 1, 1024         # init stackpointer r1
  li 2, 64           # init ro small data area anchor
  li 13, 0           # init rw small data area anchor

  # calculate faculty of 3
  li 5, 3
  bl func_fac
  stw 3, 0(13)

isr_undefined:
  my_wait
  b isr_undefined

isr_program:
  stwu 1, -2*4(1)     # saving registers used by ISR in memory
  stw 11, 4(1)
  
  li 11, 0x80
  stmw 0, 0(11)       # store all GPRs in memory

  mfsrr0 11
  addi 11, 11, 4
  mtsrr0 11

  lwz 11, 4(1)        # restore used registers
  addi 1, 1, 2*4
  rfi

#------------------------------------------------------------------------------
# Function to recursively calculate the faculty
# Input:  r5  -  argument to calculate the faculty of
# Return: r3  -  faculty of r5
#
# func_fac(x) = (x > 0) ? x * func_fac(x-1) : 1
#
func_fac:
  mflr 0              # get LNK
  stwu 1, -3*4(1)     # store back-chain word
  stw 0, 4(1)         # store LNK register
  stmw 31, 2*4(1)     # store non-volatile registers

  mr 31, 5            # copy argument to temporary register
  addic. 5, 5, -1     # subtract and test
  beq func_fac_finish # check for abort condition

  bl func_fac         # recurse

  mullw 3, 31, 3      # multiply x * func_fac(x-1)

  lwz 0, 4(1)         # load saved LNK
  mtlr 0              # restore LNK
  lmw 31, 2*4(1)      # restore non-volatile registers
  addi 1, 1, 3*4      # pop stack frame
  blr

func_fac_finish:
  trap
  li 3, 1             # fixed return value 1, no recursion

  lwz 0, 4(1)         # load saved LNK
  mtlr 0              # restore LNK
  lmw 31, 2*4(1)      # restore non-volatile registers
  addi 1, 1, 3*4      # pop stack frame
  blr
  
#------------------------------------------------------------------------------

nop
nop
nop
