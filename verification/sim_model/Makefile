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
export BUILD_SIMULATION := y
export BUILD_SIMULATOR_MODELSIM := y

all: work top_subdirs

top_subdirs:
	$(MAKE) -C $(ROOTDIR) -f $(TOP)/Makefile.build BUILDDIR=$(TOP)/$(BUILDDIR) build

$(BUILDDIR):
	mkdir $(BUILDDIR)

work:
	vlib work

clean:
	$(MAKE) -C $(ROOTDIR) -f $(TOP)/Makefile.build BUILDDIR=$(TOP)/$(BUILDDIR) rec_clean
	rm -rf work
	rm -rf $(BUILDDIR)


test: test_plt test_vector

test_plt: all
	cd $(ROOTDIR) && ./verification/test_scripts/plt_test.sh > /dev/null

test_vector: all
	cd $(ROOTDIR) && ./verification/test_scripts/fub_vector_test.sh > /dev/null


.PHONY: test test_plt test_vector
