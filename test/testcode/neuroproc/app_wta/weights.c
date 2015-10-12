// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#warning "Weight configuration for WTA"

#define W_NN    ( 100)
#define W_EI    ( 127)
#define W_IE    (-127)
#define W_STIM   (127)
#define W_STIM2   (10)

CFG_W(0,1) = W_NN;
CFG_W(0,7) = W_NN;
CFG_W(0,8) = W_EI;
CFG_W(0,9) = W_EI;
CFG_W(0,10) = W_EI;

CFG_W(1,0) = W_NN;
CFG_W(1,2) = W_NN;
CFG_W(1,8) = W_EI;
CFG_W(1,9) = W_EI;
CFG_W(1,10) = W_EI;

CFG_W(2,1) = W_NN;
CFG_W(2,3) = W_NN;
CFG_W(2,8) = W_EI;
CFG_W(2,9) = W_EI;
CFG_W(2,10) = W_EI;

CFG_W(3,2) = W_NN;
CFG_W(3,4) = W_NN;
CFG_W(3,8) = W_EI;
CFG_W(3,9) = W_EI;
CFG_W(3,10) = W_EI;
 
CFG_W(4,3) = W_NN;
CFG_W(4,5) = W_NN;
CFG_W(4,8) = W_EI;
CFG_W(4,9) = W_EI;
CFG_W(4,10) = W_EI;

CFG_W(5,4) = W_NN;
CFG_W(5,6) = W_NN;
CFG_W(5,8) = W_EI;
CFG_W(5,9) = W_EI;
CFG_W(5,10) = W_EI;

CFG_W(6,5) = W_NN;
CFG_W(6,7) = W_NN;
CFG_W(6,8) = W_EI;
CFG_W(6,9) = W_EI;
CFG_W(6,10) = W_EI;

CFG_W(7,6) = W_NN;
CFG_W(7,0) = W_NN;
CFG_W(7,8) = W_EI;
CFG_W(7,9) = W_EI;
CFG_W(7,10) = W_EI;

CFG_W(8,0) = W_IE;
CFG_W(8,1) = W_IE;
CFG_W(8,2) = W_IE;
CFG_W(8,3) = W_IE;
CFG_W(8,4) = W_IE;
CFG_W(8,5) = W_IE;
CFG_W(8,6) = W_IE;
CFG_W(8,7) = W_IE;
 
CFG_W(9,0) = W_STIM;
CFG_W(10,1) = W_STIM;
CFG_W(11,7) = W_STIM;

CFG_W(12,4) = W_STIM;
CFG_W(13,3) = W_STIM;
CFG_W(14,5) = W_STIM;


#undef W_NN
#undef W_EI
#undef W_IE
#undef W_STIM
