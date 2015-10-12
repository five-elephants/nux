// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#define MSG_RANK (1)

#include <msg.h>
#include <led.h>

#include <msg_map.h>
#include "types.h"

#ifndef SYSDEF
#	include "app_wta/sysdef.h"
#else
#	include SYSDEF
#endif  /* SYSDEF */

static const int8_t no_forward = 0;

int8_t weights[NUM_ROWS*NUM_COLS];


static void weight_update(int8_t *w, int8_t change)
{
	/*printf("weight update from %d", *w);*/

	if( *w > 0 ) {
		if( change > 0 && *w < 127 )
			*w += 1;
		else if( change < 0 && *w > 0 )
			*w -= 1;
	} else {
		if( change > 0 && *w > -127 )
			*w -= 1;
		else if( change < 0 && *w < 0 )
			*w += 1;
	}

	/*printf(" to %d\n", *w);*/
}

static void init()
{
	uint32_t i;
	for(i=0; i<NUM_ROWS*NUM_COLS; i++)
		weights[i] = no_forward;

#define CFG_W(row, col) (weights[(row)*NUM_COLS + (col)])
	#include APP_WEIGHTS
#undef CFG_W

	// configuration - start
	/*//       row           column*/
	/*weights[ 0 * NUM_COLS +  0] = 100;	*/
	/*weights[ 1 * NUM_COLS +  1] =  20;*/
	// configuration - end
}

//void start()
ENTRYPOINT
{
	uint32_t ev;
	uint16_t i;
	uint16_t j;

	/*union {*/
		/*uint32_t word;*/
		/*uint8_t bytes[4];*/
	/*} msg_out;*/
	msg_t msg_out;
	msg_t msg_in;

	init();

	led(1);

	msg_out.word = 0;

	while( 1 ) {
		// get addressed events from input
		ev = recv_msg(MSG_IN_A);	

		for(i=(ev & 0x1f) * NUM_COLS, j=0; i<((ev & 0x1f) * NUM_COLS) + NUM_COLS; i++, j++) {
			if( weights[i] != no_forward ) {
				msg_out.event.id = j;
				msg_out.event.weight = weights[i];
				/*msg_out.event.weight = 100;*/
				send_msg(MSG_OUT_A, msg_out.word);  // send to neurons
				/*send_msg(MSG_OUT_B, msg_out.word);  // send to plasticity*/

				msg_out.event.id = ev;
				send_msg(MSG_OUT_B, msg_out.word);
			}
		}

		// test for weight updates
		if( msg_waiting(MSG_IN_B) ) {
			msg_in.word = recv_msg(MSG_IN_B);
			weight_update(&weights[msg_in.update.row * NUM_COLS + msg_in.update.col],
				msg_in.update.change);
		}
	}
}
