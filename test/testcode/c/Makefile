# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


#S2PP_TOOLS=/opt/s2pp/bin/
S2PP_TOOLS=

CC=$(S2PP_TOOLS)powerpc-linux-eabi-gcc
AS=$(S2PP_TOOLS)powerpc-linux-eabi-as
LD=$(S2PP_TOOLS)powerpc-linux-eabi-ld
READELF=$(S2PP_TOOLS)powerpc-linux-eabi-readelf
OBJDUMP=$(S2PP_TOOLS)powerpc-linux-eabi-objdump
OBJCOPY=$(S2PP_TOOLS)powerpc-linux-eabi-objcopy
PAD_MEM=../../../support/pad_data_mem_file.py
PAD_BSS=bash pad_bss.sh
GEN_BINARY=$(S2PP_TOOLS)gen_binary.sh

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
CFLAGS=-Wall -msdata=none -O2 -mstrict-align -msoft-float # -fno-inline  # -Os

# Linker options
#  -static do not link against shared libraries
#  -nostdlib do not include standard libraries (I think)
#  -Ttext 0 start .text section at address 0
#LDOPTS=-static -nostdlib -Ttext 0 -Tdata 0x40000000 #--section-start system=0
LDOPTS=-static -nostdlib -T linker.txt

OBJCOPY_OPTS=-O binary --gap-fill 0 # --pad-to 0x2fff

# cshell.o must be passed first to the linker. Otherwise the reset
# symbol will not be on address 0.
ASM_OBJS=cshell.o wait_resume_isr.o
C_OBJS=hello_world.o eblinker.o time_base.o bcache_bench.o io_test.o \
			 ee_printf_test.o quicktest.o 65_wait_resume.o dbell_calculator.o \
			 selftest.o breakpoint_dummy.o
OBJS=$(ASM_OBJS) $(C_OBJS)

cshell_OBJS=cshell.o hello_world.o 
eblinker_OBJS=cshell.o eblinker.o
time_base_OBJS=cshell.o time_base.o
bcache_bench_OBJS=cshell.o bcache_bench.o
io_test_OBJS=cshell.o io_test.o
ee_printf_test_OBJS=cshell.o ee_printf_test.o
multiproc_demo_master_OBJS=cshell.o multiproc_demo_master.o
multiproc_demo_slave_OBJS=cshell.o multiproc_demo_slave.o
quicktest_OBJS=cshell.o quicktest.o
wait_resume_OBJS=cshell.o 65_wait_resume.o
dbell_calculator_OBJS=cshell.o dbell_calculator.o
selftest_OBJS=cshell.o selftest.o
breakpoint_dummy_OBJS=cshell.o breakpoint_dummy.o

TARGETS=cshell eblinker time_base bcache_bench io_test ee_printf_test \
		multiproc_demo_master multiproc_demo_slave quicktest wait_resume \
		dbell_calculator selftest breakpoint_dummy

#-----------------------------------------------------------------------------#
all: $(TARGETS)

.SECONDEXPANSION:
$(TARGETS):%:$$($$*_OBJS) Makefile
	$(LD) $(LDOPTS) -o $@ $($*_OBJS)
	$(OBJDUMP) -d $@ > $@.disas
	$(READELF) -x .text $@ | gawk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print $$i}' > $@_code.mem
	$(READELF) -x .rodata $@ | gawk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print gensub(/([0-9a-zA-Z][0-9a-zA-Z])/, "\\1 ", "g", $$i)}' > $@_data.mem
	$(READELF) -x .data $@ | gawk '/0x/{for(i=2;i<(NF<6 ? NF : 6);i++) print gensub(/([0-9a-zA-Z][0-9a-zA-Z])/, "\\1 ", "g", $$i)}' >> $@_data.mem
	#$(PAD_BSS) $@ $@_data.mem
	#$(PAD_MEM) $@_data.mem
	$(GEN_BINARY) $@ $@
	#$(OBJCOPY) $(OBJCOPY_OPTS) $@ $@.raw

$(ASM_OBJS):%.o: %.s Makefile
	$(AS) $(ASOPT) -o $@ $<

$(C_OBJS):%.o: %.c Makefile
	$(CC) $(CFLAGS) -c -o $@ $<
	$(CC) -S $(CFLAGS) -c $<

clean:
	rm -f $(OBJS)
	rm -f $(TARGETS)
	rm -f $(patsubst %,%_code.mem,$(TARGETS)) $(patsubst %,%_data.mem,$(TARGETS))
	rm -f $(patsubst %,%.disas,$(TARGETS))
	rm -f *_code.raw *_data.raw
