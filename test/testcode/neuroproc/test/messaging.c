// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#define MSG_RANK (0)

#include <msg.h>
#include <msg_map.h>
#include <stdio.h>
#include <stdlib.h>
#include <apr_general.h>

#define NUM_RANKS (3)
#define TEST_SIZE (10)

extern void __init_msg(const uint32_t _num_ranks, const uint32_t _queue_size);
extern void __clear_msg();

int main()
{
	uint32_t src, dest;
	uint32_t data[NUM_RANKS];
	uint32_t rdata[NUM_RANKS];
	uint32_t addr_out, addr_in;

	apr_initialize();
	__init_msg(NUM_RANKS, 16);
	
	for(src=0; src<NUM_RANKS; src++) {
		printf("Testing connection from %u\n",
			src);

		addr_out = MSG_OUT_A;
		for(dest=0; dest<NUM_RANKS; dest++) {
			if( src != dest ) {
				data[dest] = random();
				__send_msg(src, addr_out, data[dest]);
				printf("SEND   (%u)  0x%08x  <=  0x%08x\n",
					src, addr_out, data[dest]);
				addr_out += MSG_OUT_STEP;
			}
		}

		for(dest=0; dest<NUM_RANKS; dest++) {
			if( src != dest ) {
				addr_in = MSG_IN_A + ( (src>dest) ? (src-1) : src ) * MSG_IN_STEP;
				rdata[dest] = __recv_msg(dest, addr_in);
				printf("RECV   (%u)  0x%08x  =>  0x%08x\n",
					dest, addr_in, rdata[dest]);

				if( data[dest] != rdata[dest] ) {
					printf("Mismatch from %u to %u (send 0x%08x, got 0x%08x)\n",
						src, dest, data[dest], rdata[dest]);
				}
			}
		}
	}

	__clear_msg();	
	apr_terminate();

	return 0;
}
