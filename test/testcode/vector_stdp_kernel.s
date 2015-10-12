# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


.section .text

	li 31, NUM_SLICES*16   # load size of vector in bytes to r31
	li 1, weights@l
	li 2, wmax@l
	li 3, b@l
	li 4, c@l
	li 5, result@l
	li 6, causal@l
	li 7, acausal@l
	li 8, a@l
	li 9, v@l
	li 15, wb@l

	fxvlax 0, 0, 1   # load weights
	fxvlax 1, 0, 6   # load causal data
	fxvlax 2, 0, 7   # load acausal data
	fxvlax 31, 0, 2  # load wmax
	fxvlax 30, 0, 3  # load parameter b
	fxvlax 29, 0, 4  # load parameter c

write_back_test:
	fxvstax 0, 0, 15     # store weights to wb region
	add 15, 15, 31       # increment wb pointer
	fxvstax 1, 0, 15     # store causal data to wb region
	add 15, 15, 31       # increment wb pointer
	fxvstax 2, 0, 15     # store acausal data to wb region
	add 15, 15, 31       # increment wb counter
	fxvstax 31, 0, 15    # store wmax to wb region
	add 15, 15, 31       # increment wb pointer
	fxvstax 30, 0, 15    # store parameter b
	add 15, 15, 31       # increment wb pointer
	fxvstax 29, 0, 15    # store parameter c

stdp_kernel:
	fxvsubhm 1, 1, 2     # a(1) <- causal(1) - acausal(2)
	fxvcmph 1            # vcr <- cmp(a(1))
	fxvsubhm 2, 31, 0    # u(2) <- wmax(31) - w(0)
	fxvmulhm 3, 29, 0    # v(3) <- c(29) * w(0)
	fxvmtac 0            # acc <- w(0)
	fxvmahm 0, 1, 2, 1   # w(0) <- a(1) * u(2) + acc if vcr.gt
	fxvmahm 0, 1, 3, 2   # w(0) <- a(1) * v(3) + acc if vcr.lt
	                     # w(0) now contains:
	                     #   a * (wmax - w) + w   if a > 0
	                     #   a * (c * w) + w      if a < 0

	fxvstax 0, 0, 5      # store weights to memory
	fxvstax 1, 0, 8      # store a to memory
	fxvstax 3, 0, 9      # store v to memory

	wait


.section .data
	.align 4
	weights: .fill NUM_SLICES * 8, 2, 0x0001
	causal:  .fill NUM_SLICES * 4, 4, 0x00ff0000
	acausal: .fill NUM_SLICES * 4, 4, 0x000000ff
	wmax:    .fill NUM_SLICES * 8, 2, 0x0100
	b:       .fill NUM_SLICES * 8, 2, 0x0001
	c:       .fill NUM_SLICES * 8, 2, 0x0000

.ifdef RESULT
	wb:
		.fill NUM_SLICES * 8, 2, 0x0001
	        .fill NUM_SLICES * 4, 4, 0x00ff0000
	        .fill NUM_SLICES * 4, 4, 0x000000ff
		.fill NUM_SLICES * 8, 2, 0x0100
		.fill NUM_SLICES * 8, 2, 0x0001
		.fill NUM_SLICES * 8, 2, 0x0000

	result:  .fill NUM_SLICES * 4, 4, 0xfe020001
	a:       .fill NUM_SLICES * 4, 4, 0x00ffff01
	v:       .fill NUM_SLICES * 4, 4, 0x00000000
.else
	wb:      .fill NUM_SLICES * 6*8, 2, 0x0000
	result:  .fill NUM_SLICES * 8, 2, 0x0000
	a:       .fill NUM_SLICES * 8, 2, 0x0000
	v:       .fill NUM_SLICES * 4, 4, 0x00000000
.endif

