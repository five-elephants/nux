// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#define MSG_RANK (2)

#include <msg.h>
#include <msg_map.h>
#include <time_base.h>
#include "fxdpt.h"
#include "exp.h"
#include "types.h"

/* XXX this belongs into syslib */
#ifdef PLATFORM_LINUX
/*#	include <pthread.h>*/
#	include <sched.h>
#	include <stdio.h>
/*#	define YIELD pthread_yield();*/
#	define YIELD sched_yield();
#else
#	define YIELD
#endif  /* PLATFORM_LINUX */

#ifndef SYSDEF
#	include "app_wta/sysdef.h"
#else
#	include SYSDEF
#endif  /* SYSDEF */

#define INDEX(row,col) (row*NUM_COLS + col)
#define ABS(x) ( (x>=0) ? x : -x )
//--------------------------------------------------------------------------------
typedef struct {
	/*int32_t pos;*/
	/*int32_t neg;*/
	int16_t pos;
	int16_t neg;
} accum_t;

time_base_t pre_timer[NUM_ROWS];
time_base_t post_timer[NUM_COLS];
accum_t accum[NUM_ROWS*NUM_COLS];
volatile time_base_t t_compute_synplast;
//--------------------------------------------------------------------------------

static int32_t stdp_model(time_base_t pre, time_base_t post)
{
	static const int32_t ap =  100;
	static const int32_t am = -100;
	static const int32_t tp = 20;
	static const int32_t tm = 20;
	static const int32_t max_pre_post = FP(220.0); 
	static const int32_t max_post_pre = FP(220.0); 

	int32_t rv = 0;
	int32_t dt;
	int32_t pre_post_ms;
	/*int32_t pre_ms, post_ms;*/

	pre /= MS;
	post /= MS;
	if( ABS((int64_t)pre - (int64_t)post) > 65536 )
		return 0;

	pre_post_ms = FP((int64_t)pre - (int64_t)post);

	/*pre_ms = FP(pre);*/
	/*post_ms = FP(post);*/

	/*printf("STDP pre_post_ms = %f (%d) [max_pre_post=%f (%d), max_post_pre=%f (%d)]\n",*/
		/*INV_FP(pre_post_ms), pre_post_ms, INV_FP(max_pre_post), max_pre_post,*/
		/*INV_FP(max_post_pre), max_post_pre);*/
	/*printf("STDP: pre_ms (%f) - post_ms (%f) = %f\n",*/
		/*INV_FP(pre_ms), INV_FP(post_ms), INV_FP(pre_ms - post_ms));*/
	/*printf("STDP: pre_ms (%d) - post_ms (%d) = %d\n",*/
		/*(pre_ms), (post_ms), (pre_ms - post_ms));*/

	if( (pre_post_ms > 0) && (pre_post_ms < max_pre_post) ) {
	/*if( (pre_ms > post_ms) && (ABS(pre_ms-post_ms) < max_pre_post) ) {*/
		/*dt = pre_ms - post_ms;*/
		dt = pre_post_ms;
		dt = dt/tm;   // divide time constant
		rv = am * exp_6b(-dt);  // calculate exponential
		/*rv = rv / INV_SCALE;  // rescale after fixedpoint multiplication*/

		/*printf("STDP- = %f (dt/tau=%f, pre_post_ms=%f)\n",*/
			/*INV_FP(rv), INV_FP(dt), INV_FP(pre_post_ms));*/
	} 

	if( pre_post_ms == 0 )
		rv = 0;
	
	if( (pre_post_ms < 0) && (-pre_post_ms < max_post_pre) ) {
	/*if( (pre_ms < post_ms) && (ABS(post_ms-pre_ms) < max_post_pre) ) {*/
		/*dt = (int32_t)(post_ms - pre_ms);*/
		dt = -pre_post_ms;
		dt = dt/tp;   // divide time constant
		rv = ap * exp_6b(-dt);  // calculate exponential
		/*rv = rv / INV_SCALE;  // rescale after fixedpoint multiplication*/

		/*printf("STDP+ = %f (dt/tau=%f, pre_post_ms=%f)\n",*/
			/*INV_FP(rv), INV_FP(dt), INV_FP(pre_post_ms));*/
	}

	return rv;
}

static void test_accum(accum_t* acc, int i, int j)
{
	static const int16_t thresh_pos = FP16(1000.0);
	static const int16_t thresh_neg = FP16(1000.0);

	msg_t msg;

	msg.update.padding = 0;
	msg.update.row = i;
	msg.update.col = j;

	if( acc->pos > thresh_pos ) {
		/*printf("(%d, %d) : pos over thresh\n", i, j);*/
		acc->pos -= thresh_pos;

		msg.update.change = 1;
		send_msg(MSG_OUT_B, msg.word);	
	} /*else 
		printf("(%d, %d) : pos = %f\n", i, j, INV_FP(acc->pos));*/

	if( acc->neg > thresh_neg ) {
		/*printf("(%d, %d) : neg over thresh\n", i, j);*/
		acc->neg -= thresh_neg;

		msg.update.change = -1;
		send_msg(MSG_OUT_B, msg.word);	
	} /*else
		printf("(%d, %d) : neg = %f\n", i, j, INV_FP(acc->neg));*/
}

ENTRYPOINT
{
	static const time_base_t test_period = 100*MS;
	
	int i, j;
	msg_t msg;
	time_base_t cur_t;
	time_base_t compute_start;
	time_base_t last_test;

	for(i=0; i<NUM_ROWS*NUM_COLS; i++)
		accum[i] = (accum_t) { .pos = 0, .neg = 0 };
				
	t_compute_synplast = 0;

	while( 1 ) {
		compute_start = get_time_base();

		// get pre-events
		if( msg_waiting(MSG_IN_B) ) {
			msg.word = recv_msg(MSG_IN_B);

			cur_t = get_time_base();
			pre_timer[msg.event.id] = cur_t;
			/*printf("Setting pre_timer[%u] = %lu\n",*/
				/*msg.event.id, cur_t);*/

			for(i=0; i<NUM_COLS; i++) {
				accum[INDEX(msg.event.id, i)].neg -= 
					fxdpt_32_to_16_bits(stdp_model(cur_t, post_timer[i]));
			}
		}

		// get post-events
		if( msg_waiting(MSG_IN_A) ) {
			msg.word = recv_msg(MSG_IN_A);

			cur_t = get_time_base();
			post_timer[msg.event.id] = cur_t;
			/*printf("Setting post_timer[%u] = %lu\n",*/
				/*msg.event.id, cur_t);*/

			for(i=0; i<NUM_ROWS; i++) {
				accum[INDEX(i, msg.event.id)].pos +=
					fxdpt_32_to_16_bits(stdp_model(pre_timer[i], cur_t));
			}
		}

		// check threshold
		cur_t = get_time_base();
		if( (cur_t - last_test) > test_period ) {
			for(i=0; i<NUM_ROWS; i++) {
				for(j=0; j<NUM_COLS; j++) {
					test_accum(&accum[INDEX(i,j)], i, j);
				}
			}
		}

		t_compute_synplast = (t_compute_synplast + (get_time_base() - compute_start))/2;

		YIELD
	}
}
