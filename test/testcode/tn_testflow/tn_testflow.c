// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#ifndef TN_TEST_INC
	#include "operators.h"
#else
	#include TN_TEST_INC
#endif


int start() {
	
//	int* mem;
//	mem = 0x10;
	int i;
	//zu testende funktion
	for(i=0; i<size; i++){
		mem[i] = 0;

	}

	test_funktion();
	

return 0;
}
