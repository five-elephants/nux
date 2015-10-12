# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


include ../Makefile.srclist

M4=m4
M4_INCLUDE_DIR=../m4

SYNPLIFY=synplify_premier_dp
SYNPLIFY_FPGA_PRJ=syn/p1.prj
SYNPLIFY_FPGA_SRCLIST=syn/p1_srclist.txt
#SYNPLIFY_FPGA_PROJECT=syn/p1_project.tcl
SYNPLIFY_FPGA_PROJECT=syn/emsys_project.tcl

SYNOPSYS_DW_PATH=$(SYNOPSYS)/dw

# options for bitfile generation
#NCD_FILE=syn/ml505/xilinx_par/Fpga_top.ncd
NCD_FILE=syn/ml505/xilinx_par/Emsys_top.ncd
BOOT_IMG=../test/testcode/c/eblinker_code.mem
DATA_IMG=../test/testcode/c/eblinker_data.mem

all: synplify

gui: synplify_gui

synplify_gui: synplify_project
	$(SYNPLIFY) $(SYNPLIFY_FPGA_PRJ)

synplify: synplify_project
	$(SYNPLIFY) -batch -runall $(SYNPLIFY_FPGA_PRJ)

synplify_srclist: ../Makefile.srclist Makefile $(S2PP_PREPROC_SRC)
	@rm -rf $(SYNPLIFY_FPGA_SRCLIST)
	#@$(foreach i,$(DW_SRC), echo -e "add_file -verilog \"$(SYNOPSYS_DW_PATH)/$i\"" >> $(SYNPLIFY_FPGA_SRCLIST);)
	@$(foreach i,$(S2PP_SRC), echo -e "add_file -verilog -vlog_std sysv \"../../$i.sv\"" >> $(SYNPLIFY_FPGA_SRCLIST);)
	@$(foreach i,$(S2PP_PREPROC_SRC), echo -e "add_file -verilog -vlog_std sysv \"../../$i.preproc.sv\"" >> $(SYNPLIFY_FPGA_SRCLIST);)
	@$(foreach i,$(S2PP_FPGA_SRC), echo -e "add_file -verilog -vlog_std sysv \"../../$i.sv\"" >> $(SYNPLIFY_FPGA_SRCLIST);)
	@$(foreach i,$(FPGA_COREGEN_SRC), echo -e "add_file -verilog \"../../$i.v\"" >> $(SYNPLIFY_FPGA_SRCLIST);)
	@$(foreach i,$(FPGA_COREGEN_SRC), echo -e "add_file \"../../$i.ngc\"" >> $(SYNPLIFY_FPGA_SRCLIST);)
	@echo "*** Created source list for synplify: $(SYNPLIFY_FPGA_SRCLIST)"

synplify_project: $(SYNPLIFY_FPGA_PROJECT) synplify_srclist Makefile
	@rm -rf $(SYNPLIFY_FPGA_PRJ)
	@echo "source \"$(notdir $(SYNPLIFY_FPGA_SRCLIST))\" " > $(SYNPLIFY_FPGA_PRJ)
	@echo "source \"$(notdir $(SYNPLIFY_FPGA_PROJECT))\" " >> $(SYNPLIFY_FPGA_PRJ)
	@echo "*** Created project file for synplify: $(SYNPLIFY_FPGA_PRJ)"


bit: $(NCD_FILE)
	#bitgen -w $(NCD_FILE) -bd $(BOOT_IMG) tag imem -bd $(DATA_IMG) tag dmem
	bitgen -w $(NCD_FILE)


$(S2PP_PREPROC_SRC):%:../%.sv
	$(M4) -I $(M4_INCLUDE_DIR) $< > ../$@.preproc.sv
