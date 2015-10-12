# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


AS=powerpc-linux-eabi-as
LD=powerpc-linux-eabi-ld
OBJCOPY=powerpc-linux-eabi-objcopy

LD_FLAGS=-T c/linker.txt
AS_FLAGS=-mpower7 --defsym NUM_SLICES=8
RESULT_SYM=--defsym RESULT=1
OBJCOPY_FLAGS=-O binary


RAW_PROGRAMS=fxv_test vector_stdp_kernel sync


.PHONY: all
all: $(RAW_PROGRAMS)


$(RAW_PROGRAMS):%:%.s
	$(AS) $(AS_FLAGS) $< -o $@.o
	$(LD) $(LD_FLAGS) $@.o -o $@.elf
	$(OBJCOPY) $(OBJCOPY_FLAGS) --only-section .text $@.elf $@_code.raw
	$(OBJCOPY) $(OBJCOPY_FLAGS) --remove-section .text $@.elf $@_data.raw
	$(AS) $(AS_FLAGS) $(RESULT_SYM) $< -o $@.o
	$(LD) $(LD_FLAGS) $@.o -o $@.elf
	$(OBJCOPY) $(OBJCOPY_FLAGS) --remove-section .text $@.elf $@_exp.raw


clean:
	rm $@.o
	rm $@.elf
