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
#include <led.h>
#include <time_base.h>

#include <msg_map.h>
#include "fxdpt.h"
#include "types.h"

#ifndef SYSDEF
#	include "app_wta/sysdef.h"
#else
#	include SYSDEF
#endif  /* SYSDEF */

#define NO_FORWARD (0xff)

typedef struct {
	uint16_t t_ms;
	uint8_t padding;
	uint8_t id;
} event_t; 

typedef struct {
	uint32_t rate;
	uint8_t dest_row;
} rbg_t;

static const time_base_t stim_test_period = 1*MS;
static const time_base_t integration_period = 1*MS;

int32_t membrane[NUM_COLS];
uint8_t dest_row[NUM_COLS];
event_t ev_record[EV_RECORD_SIZE];
volatile uint32_t ev_record_end;
rbg_t rbgs[NUM_RBG];
int32_t membrane_record[MEMBRANE_RECORD_SIZE];
volatile uint32_t membrane_record_end;
volatile time_base_t t_compute;

/** This is a random number generator called multiply with carry (MWC) as
 * proposed by George Marsaglia. */
uint32_t random()
{
	static uint32_t z = 521288629;
	static uint32_t w = 362436069;

	z = 36969 * (z & 65535) + (z >> 16);
	w = 18000 * (w & 65535) + (w >> 16);
	return (z << 16) + w;
}

//--------------------------------------------------------------------------------
// Leaky integrate and fire model
//--------------------------------------------------------------------------------

typedef struct {
	int32_t tau_mem_inv;
	int32_t v_leak;
	int32_t v_reset;
	int32_t v_thresh;
	int32_t v_exc;
	int32_t v_inh;
} lif_param_t;

lif_param_t params[NUM_COLS];

static int32_t lif_accumulate_input(const uint8_t index, const int32_t acc, const int8_t weight_in)
{
	static const int32_t tau_max_inv = FP( (1.0/1.0e-3) / 256.0 );

	int32_t g = weight_in * tau_max_inv;

	if( weight_in > 0 ) 
		return acc + g * (params[index].v_exc - membrane[index]);
	else
		return acc - g * (params[index].v_inh - membrane[index]);

	return 0;
}

static uint8_t neuron_lif(const uint8_t index, int32_t input)
{
	static const int32_t dt = FP(1.0e-3);

	int32_t dv;
	int32_t fp_in;

	dv = (params[index].v_leak - membrane[index])*params[index].tau_mem_inv;
	dv = dv/INV_SCALE;
	dv += input;

	/*if( (index == 4) && (membrane_record_end < MEMBRANE_RECORD_SIZE) )*/
		/*membrane_record[membrane_record_end++] = dv;*/

	/*dv = (input > 0) ? g_max : 0;*/
	membrane[index] += (dt*dv)/INV_SCALE;

	if( membrane[index] > params[index].v_thresh ) {
		membrane[index] = params[index].v_reset;
		return 1;
	}

	/* Parrot mode */
	/*if( input != 0 ) {*/
		/*membrane[index] = params[index].v_reset;*/
		/*return 1;*/
	/*}*/

	return 0;
}

//--------------------------------------------------------------------------------
static void init()
{
	uint32_t i;

	for(i=0; i<EV_RECORD_SIZE; i++) {
		ev_record[i].t_ms = i;
		ev_record[i].id = 0;
		ev_record[i].padding = 0;
	}
	
	for(i=0; i<NUM_COLS; i++) {
		dest_row[i] = NO_FORWARD;
		params[i].tau_mem_inv = FP(1.0/600.0e-3);
		params[i].v_leak = FP(-70.0e-3);
		params[i].v_reset = FP(-80.0e-3);
		params[i].v_thresh = FP(-50.0e-3);
		params[i].v_exc = FP(-20.0e-3);
		params[i].v_inh = FP(-120.0e-3);
		membrane[i] = params[i].v_reset;
	}

	for(i=0; i<NUM_RBG; i++) {
		rbgs[i].rate = 0;
		rbgs[i].dest_row = NO_FORWARD;
	}

	#include APP_NEURONS
}
//--------------------------------------------------------------------------------

//void start()
ENTRYPOINT
{
	msg_t msg_in;

	uint32_t ev_out;
	time_base_t cur_t;
	time_base_t last_stim;
	time_base_t last_integrate;
	time_base_t last_timed;
	time_base_t t_start;
	uint16_t cur_t_ms16;
	uint32_t led_state = 0;
	int32_t i;
	int32_t cum_input[NUM_COLS];

	ev_record_end = 0;
	membrane_record_end = 0;
	t_compute = 0;

	init();

	led(led_state);

	last_stim = get_time_base();
	last_integrate = last_stim;
	t_start = last_stim;

	for(i=0; i<NUM_COLS; i++)
		cum_input[i] = 0;	

	while( 1 ) {
		cur_t = get_time_base();
		cur_t_ms16 = millisecond_16();

		while( msg_waiting(MSG_IN_A) ) {
			msg_in.word = recv_msg(MSG_IN_A);	
			/*cum_input[msg_in.event.id] += msg_in.event.weight;*/
			cum_input[msg_in.event.id] = lif_accumulate_input(msg_in.event.id,
					cum_input[msg_in.event.id],
					msg_in.event.weight);

			/*if( (msg_in.event.id == 4) && (membrane_record_end < MEMBRANE_RECORD_SIZE) )*/
				/*membrane_record[membrane_record_end++] = cum_input[msg_in.event.id];*/
		}

		// integrate neurons
		if( (cur_t - last_integrate) > integration_period ) {
			for(i=0; i<NUM_COLS; i++) {
				if( neuron_lif(i, cum_input[i]) ) {
					// produce output event
					if( dest_row[i] != NO_FORWARD ) {
						ev_out = dest_row[i];
						send_msg(MSG_OUT_A, ev_out);

						led_state = ~led_state;
						led(led_state);
					}

					ev_out = i;
					send_msg(MSG_OUT_B, ev_out);  // send to plasticity

					// record event
					if( ev_record_end < EV_RECORD_SIZE ) {
						ev_record[ev_record_end].id = i;
						ev_record[ev_record_end].t_ms = cur_t_ms16;
						++ev_record_end;
					}
				}

				cum_input[i] = 0;
			}
			
			// record membrane
			if( membrane_record_end < MEMBRANE_RECORD_SIZE )
				membrane_record[membrane_record_end++] = membrane[MEMBRANE_RECORD_INDEX];

			last_integrate = cur_t;
		}

		// generate independent stimulus
		if( (cur_t - last_stim) > stim_test_period ) {
			for(i=0; i<NUM_RBG; i++) {
				if( random() < rbgs[i].rate ) {
					ev_out = rbgs[i].dest_row;
					send_msg(MSG_OUT_A, ev_out);

#ifdef OPT_RECORD_RBGS
					if( ev_record_end < EV_RECORD_SIZE ) {
						ev_record[ev_record_end].id = i + 0x80;
						ev_record[ev_record_end].t_ms = cur_t_ms16;
						++ev_record_end;
					}
#endif  /* OPT_RECORD_RBGS */
				}
			}
		
			last_stim = cur_t;
		}

#ifdef APP_TIMED
#	include APP_TIMED
#endif  /* APP_TIMED */

		t_compute = (t_compute + (get_time_base() - cur_t))/2;
	}
}
