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

ifndef S2PP_TOOLS
	powerpc_gcc=$(shell which powerpc-linux-eabi-gcc)
	S2PP_TOOLS=$(shell dirname $(powerpc_gcc))
endif

CC=$(S2PP_TOOLS)/powerpc-linux-eabi-gcc
AS=$(S2PP_TOOLS)/powerpc-linux-eabi-as
LD=$(S2PP_TOOLS)/powerpc-linux-eabi-ld
READELF=$(S2PP_TOOLS)/powerpc-linux-eabi-readelf
OBJDUMP=$(S2PP_TOOLS)/powerpc-linux-eabi-objdump
PAD_MEM=../../../support/pad_data_mem_file.py
PAD_BSS=bash pad_bss.sh
GEN_BINARY=$(S2PP_TOOLS)/gen_binary.sh

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
CFLAGS+=-I./syslib

# Linker options
#  -static do not link against shared libraries
#  -nostdlib do not include standard libraries (I think)
#  -Ttext 0 start .text section at address 0
#LDOPTS=-static -nostdlib -Ttext 0 -Tdata 0x40000000 #--section-start system=0
#LDOPTS=-static -nostdlib -T linker.txt -L$(S2PP_TOOLS)/../lib/gcc/powerpc-linux-eabi/4.6.2 
LDOPTS=-static -nostdlib -T linker.txt -L$(S2PP_TOOLS)/../lib/gcc/powerpc-linux-eabi/4.5.0 
LIBS=-lgcc

# cshell.o must be passed first to the linker. Otherwise the reset
# symbol will not be on address 0.
ASM_OBJS=cshell.o
C_OBJS=synarray.o neuron.o synplast.o exp.o
OBJS=$(ASM_OBJS) $(C_OBJS)

synarray_OBJS=cshell.o synarray.o 
neuron_OBJS=cshell.o neuron.o
synplast_OBJS=cshell.o synplast.o exp.o
single_neuron_OBJS=cshell.o single_neuron.o

TARGETS=synarray neuron synplast single_neuron

ifndef SYSDEF
	D_SYSDEF="\"app_wta/sysdef.h\""
else
	D_SYSDEF="\"$(SYSDEF)\""
endif

CFLAGS+=-DSYSDEF=$(D_SYSDEF) -DENTRYPOINT="void start()" -DPLATFORM_S2PP
#-----------------------------------------------------------------------------#
all: $(TARGETS)

.SECONDEXPANSION:
$(TARGETS):%:$$($$*_OBJS) Makefile
	$(LD) $(LDOPTS) -o $@ $($*_OBJS) $(LIBS)
	$(OBJDUMP) -d $@ > $@.disas
	#$(GEN_BINARY) $@ $@

$(ASM_OBJS):%.o: %.s Makefile
	$(AS) $(ASOPT) -o $@ $<

$(C_OBJS):%.o: %.c Makefile
	$(CC) $(CFLAGS) -c -o $@ $<
	$(CC) -S $(CFLAGS) -c $<

clean:
	rm -f $(OBJS)
	rm -f $(TARGETS)
	#rm -f $(patsubst %,%_code.mem,$(TARGETS)) $(patsubst %,%_data.mem,$(TARGETS))
	rm -f $(patsubst %,%.disas,$(TARGETS))
	rm -f *_code.raw *_data.raw
