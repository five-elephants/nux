// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#warning "Timed configuration for STDP"

int fired;
int once = 0;

if( (cur_t - last_timed) > 100*MS ) {
	send_msg(MSG_OUT_A, 0);
	last_timed = cur_t;
	fired = 0;
}

if( !fired && ((cur_t - last_timed) > 20*MS) ) {
	send_msg(MSG_OUT_A, 1);
	send_msg(MSG_OUT_A, 2);
	send_msg(MSG_OUT_A, 3);
	send_msg(MSG_OUT_A, 4);
	fired = 1;
}
