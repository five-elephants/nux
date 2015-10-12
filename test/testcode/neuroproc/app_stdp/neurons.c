// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#warning "Neuron configuration for STDP"

params[0].v_thresh = FP(-60.0e-3);
params[0].v_leak = FP(-75.0e-3);
params[0].v_reset = FP(-75.0e-3);

//dest_row[0] = 0;

/*rbgs[0].rate = 4294967296 * 0.1;*/
/*rbgs[0].dest_row = 0;*/

