# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


include config

export TOP := $(CURDIR)
export CONFIGFILE := $(ROOTDIR)/.config
export BUILD_SIMULATION := n
export BUILD_SIMULATOR_MODELSIM := n

VERSION=v2
RESULTSDIR=results
export RESULT_FILE=$(CURDIR)/$(RESULTSDIR)/pu_core.sv

.PHONY: all
all: $(RESULT_FILE)

top_subdirs:
	$(MAKE) -C $(ROOTDIR) -f $(TOP)/Makefile.build BUILDDIR=$(TOP)/$(BUILDDIR) build

.PHONY: header
header: $(RESULTSDIR)
	rm -f $(RESULT_FILE)
	touch $(RESULT_FILE)
	cat $(ROOTDIR)/src/rtl/include/workarounds.svh >> $(RESULT_FILE)

$(RESULT_FILE): header top_subdirs Makefile
	@cat $(RESULT_FILE) | sed "s/\`include \"workarounds.svh\"//g" > $(RESULT_FILE).tmp
	@mv $(RESULT_FILE).tmp $(RESULT_FILE)

$(BUILDDIR): $(RUNDIR)
	mkdir -p $(BUILDDIR)

$(RESULTSDIR):
	mkdir -p $(RESULTSDIR)

.PHONY: clean
clean:
	$(MAKE) -C $(ROOTDIR) -f $(TOP)/Makefile.build BUILDDIR=$(TOP)/$(BUILDDIR) rec_clean
	rm -f $(RESULT_FILE)
	rm -rf $(BUILDDIR)
