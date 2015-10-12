# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


#PREFIX=/afsuser/sfriedma/local
PREFIX=/afsuser/tnonne/local

CXXFLAGS=-I$(PREFIX)/include -ggdb
LDFLAGS=-L$(PREFIX)/lib -lurjtag -lboost_program_options
PAD_MEM=/afs/kip.uni-heidelberg.de/user/tnonne/s2pp-source/support/pad_data_mem_file.py

read_dmem_OBJS=read_dmem.o

all: read_dmem 

read_dmem: $(read_dmem_OBJS) Makefile
	g++ -o $@ $(LDFLAGS) $(read_dmem_OBJS)

sub:
	./read_dmem --size=8192 -f ergebnis.txt

clean:
	rm -f *.o
	rm read_dmem
