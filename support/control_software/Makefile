# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


PREFIX=/afs/kip.uni-heidelberg.de/user/tnonne/s2pp-source/test/testcode/c
TEMP_MEM=/afs/kip.uni-heidelberg.de/user/tnonne/s2pp-source/test/testcode/c/temp_mem_ad.txt
TEMP_TIMER=/afs/kip.uni-heidelberg.de/user/tnonne/s2pp-source/test/testcode/c/temp_timer_ad.txt
REFERENZ=/afs/kip.uni-heidelberg.de/user/tnonne/s2pp-source/test/testcode/c/endianneu.txt
JTAG=jtag_client

TARGET=matrix_prog.svf

all: $(TARGET)

$(TARGET): Makefile
	cp -v $(PREFIX)/$(TARGET) $(TARGET)
	rm -f program.svf
	ln -s $(TARGET) program.svf
	cp $(TEMP_MEM) temp_mem_ad.txt
	cp $(TEMP_TIMER) temp_timer_ad.txt
	cp $(REFERENZ) referenzsystem.txt
	jtag program

dump:
	make -C jtag_client sub
	cat $(JTAG)/ergebnis.txt| awk '{for(i=1;i<(NF+1);i++) print gensub(/([0-9a-zA-Z][0-9a-zA-Z])/, "\\1 ", "g", $$i)}' > result_byte.txt 

clean:
	rm -f program.svf
	rm -f $(TARGET)
	rm -f temp_mem_ad.txt
	rm -f referenzsystem.txt
	rm -f result_byte.txt
	rm -f $(JTAG)/ergebnis.txt
