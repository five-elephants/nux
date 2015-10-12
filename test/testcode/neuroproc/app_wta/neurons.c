// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#warning "Neuron configuration for WTA"

for(i=0; i<NUM_COLS; i++) {
	params[i].v_thresh = FP(-60.0e-3);
}

for(i=8; i<11; i++) {
	params[i].v_leak = FP(-65.0e-3);
	params[i].v_reset = FP(-65.0e-3);
}

dest_row[0] = 0;
dest_row[1] = 1;
dest_row[2] = 2;
dest_row[3] = 3;
dest_row[4] = 4;
dest_row[5] = 5;
dest_row[6] = 6;
dest_row[7] = 7;
dest_row[8] = 8;
dest_row[9] = 8;
dest_row[10] = 8;


rbgs[0].rate = 4294967296 * 0.1;
rbgs[0].dest_row = 9;

rbgs[1].rate = 4294967296 * 0.0075;
rbgs[1].dest_row = 10;

rbgs[2].rate = 4294967296 * 0.0075;
rbgs[2].dest_row = 11;


rbgs[3].rate = 4294967296 * 0.4;
rbgs[3].dest_row = 12;

rbgs[4].rate = 4294967296 * 0.03;
rbgs[4].dest_row = 13;

rbgs[5].rate = 4294967296 * 0.03;
rbgs[5].dest_row = 14;
