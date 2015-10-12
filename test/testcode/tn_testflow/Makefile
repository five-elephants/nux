# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


NM=powerpc-linux-eabi-nm
CC=powerpc-linux-eabi-gcc
AS=powerpc-linux-eabi-as
LD=powerpc-linux-eabi-ld
READELF=powerpc-linux-eabi-readelf
OBJDUMP=powerpc-linux-eabi-objdump
PAD_MEM=../../../support/pad_data_mem_file.py
FPGA=../../../support/svf_programmer.py

# assembler options: 
#  --warn warnings on
#  -a32 generate ELF32
#  -many code for any architecture (PWR/PWRX/PPC)
#  -mbig big endian mode
ASOPT=--warn -a32 -many -mbig

# C compiler options:
#  -Wall all warnings on
#  -Os optimize for size (can generate calls to library code for out-of-line register saving)
#  -msdata=none don't use the sdata section
#  -mblock-move-inline-limit= number of bytes moved inline before calling out to memcpy/memmove
# CFLAGS=-Wall -msdata=none -O2 # -fno-inline  # -Os
CFLAGS=-Wall -msdata=none -O2 -g  # -mblock-move-inline-limit=100000 #-Os
CFLAGS+=-mpowerpc -mcpu=common -mtune=405 -mmultiple -popcntb -mstrict-align

# Linker options
#  -static do not link against shared libraries
#  -nostdlib do not include standard libraries (I think)
#  -Ttext 0 start .text section at address 0
LDOPTS=-static -nostdlib -T linker.txt  #-M -Ttext 0# -Tdata 0x40000000 -Tbss 0x40000800 --section-start .rodata=0x40001000 #--section-start system=0

# cshell.o must be passed first to the linker. Otherwise the reset
# symbol will not be on address 0.
ASM_OBJS=cshell.o
C_OBJS=hello_world.o eblinker.o tn_testflow.o
OBJS=$(ASM_OBJS) $(C_OBJS)

cshell_OBJS=cshell.o hello_world.o 
eblinker_OBJS=cshell.o eblinker.o
tn_testflow_OBJS=cshell.o tn_testflow.o
fibonacci_OBJS=cshell.o fibonacci.o
operators_OBJS=cshell.o operators.o
prime_OBJS=cshell.o prime.o
switch_OBJS=cshell.o switch.o

TARGETS=fibonacci operators prime switch

fibonacci_INC=fibonacci.h
operators_INC=operators.h
prime_INC=prime.h
switch_INC=switch.h

TEST_OBJS=fibonacci.o operators.o prime.o switch.o

TEST_FUNCS=fibonacci.h \
		   operators.h \
		   prime.h \
		   switch.h

#-----------------------------------------------------------------------------#
all: $(TARGETS)

.SECONDEXPANSION:
$(TARGETS):%:$$($$*_OBJS) $$($$*_INC) Makefile
	$(LD) $(LDOPTS) -o $@ $($*_OBJS)
	$(OBJDUMP) -d $@ > $@.disas
	$(READELF) -x .text $@ | awk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print $$i}' > $@_code.mem
	$(READELF) -x .data $@ | awk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print gensub(/([0-9a-zA-Z][0-9a-zA-Z])/, "\\1 ", "g", $$i)}' > $@_hex_data.mem
	$(PAD_MEM) $@_hex_data.mem
	$(READELF) -x .bss $@ | awk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print gensub(/([0-9a-zA-Z][0-9a-zA-Z])/, "\\1 ", "g", $$i)}' > $@_hex_bss.mem
	$(PAD_MEM) $@_hex_bss.mem
	$(READELF) -x .rodata $@ | awk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print gensub(/([0-9a-zA-Z][0-9a-zA-Z])/, "\\1 ", "g", $$i)}' > $@_hex_rodata.mem
	$(PAD_MEM) $@_hex_rodata.mem
	$(READELF) -x .sbss $@ | awk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print gensub(/([0-9a-zA-Z][0-9a-zA-Z])/, "\\1 ", "g", $$i)}' > $@_hex_sbss.mem
	cat $@_hex_rodata.mem > $@_data.mem
	cat $@_hex_data.mem >> $@_data.mem
	cat $@_hex_sbss.mem >> $@_data.mem
	cat $@_hex_bss.mem >> $@_data.mem
	$(NM) -n $@|grep -w 'mem'|awk '{print $$1}' > $@_temp_mem_ad.txt
	$(NM) -n $@|grep -w 'time_measured'|awk '{print $$1}' > $@_temp_timer_ad.txt
	$(FPGA) $@_code.mem $@_data.mem > $@_prog.svf
	#$(READELF) -x .data $@ | awk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print gensub(/([0-9a-zA-Z][0-9a-zA-Z])/, "\\1 ", "g", $$i)}' > $@_data.mem
	#$(PAD_MEM) $@_data.mem

compare:
	gcc -DTN_TEST_INC=\"$(FUNCTION).h\" -DTN_DUMP_FILE=\"../../../dump_tn_testflow_$(FUNCTION).mem\" -DTEMP_MEM_AD_FILE=\"$(FUNCTION)_temp_mem_ad.txt\" -o tn_compare tn_compare.c
	./tn_compare

$(ASM_OBJS):%.o: %.s Makefile
	$(AS) $(ASOPT) -o $@ $<

$(C_OBJS):%.o: %.c Makefile
	$(CC) $(CFLAGS) -c -o $@ $<
	$(CC) $(CFLAGS) -S -o $@.s $<

$(TEST_OBJS):%.o: %.h Makefile
	$(CC) $(CFLAGS) -DTN_TEST_INC=\"$(patsubst %.o,%.h,$@)\" -c -o $@ tn_testflow.c

clean:
	rm -f $(OBJS)
	rm -f $(TARGETS)
	rm -f $(patsubst %,%_code.mem,$(TARGETS)) $(patsubst %,%_data.mem,$(TARGETS))
	rm -f $(patsubst %,%.disas,$(TARGETS))
	rm -f $(patsubst %,%_prog.svf,$(TARGETS))
	rm -f $(patsubst %,%_hex_*.mem,$(TARGETS))
	rm -f $(patsubst %,%_temp_mem_ad.txt,$(TARGETS))

.PHONY:	compare
