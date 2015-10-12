// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#include <stdint-gcc.h>
#include <time_base.h>
#include <led.h>

#include "fxdpt.h"
#include "types.h"

#define NO_FORWARD (0xff)

#define NUM_RBG (1)
#define NUM_ROWS (1)
#define NUM_COLS (1)

typedef struct {
	uint32_t rate;
	uint8_t dest_row;
} rbg_t;

static const time_base_t integration_period = 1*MS;
static const time_base_t stim_test_period = 1*MS;
static const int8_t no_forward = 0;

int8_t weights[NUM_ROWS*NUM_COLS];
uint8_t dest_row[NUM_COLS];
volatile int32_t membrane[NUM_COLS];
rbg_t rbgs[NUM_RBG];
volatile uint32_t last_membrane_write;

/** This is a random number generator called multiply with carry (MWC) as
 * proposed by George Marsaglia. */
static uint32_t random()
{
	static uint32_t z = 521288629;
	static uint32_t w = 362436069;

	z = 36969 * (z & 65535) + (z >> 16);
	w = 18000 * (w & 65535) + (w >> 16);
	return (z << 16) + w;
}
//
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
	/*int32_t fp_in;*/

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

	for(i=0; i<NUM_ROWS*NUM_COLS; i++)
		weights[i] = no_forward;

#define CFG_W(row, col) (weights[(row)*NUM_COLS + (col)])
	CFG_W(0,0) = 10;
#undef CFG_W

	for(i=0; i<NUM_COLS; i++) {
		dest_row[i] = NO_FORWARD;
		params[i].tau_mem_inv = FP(1.0/100.0e-3);
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

	rbgs[0].rate = 4294967296 * 0.01;
	rbgs[0].dest_row = 0;
}
//--------------------------------------------------------------------------------

void start() 
{
	time_base_t cur_t;
	time_base_t last_stim;
	time_base_t last_integrate;
	time_base_t t_start;
	uint16_t cur_t_ms16;
	uint32_t led_state = 0;
	int32_t i;
	int32_t cum_input[NUM_COLS];

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

		// integrate neurons
		if( (cur_t - last_integrate) > integration_period ) {
			for(i=0; i<NUM_COLS; i++) {
				if( neuron_lif(i, cum_input[i]) ) {
					// produce output event
					if( dest_row[i] != NO_FORWARD ) {
						/*ev_out = dest_row[i];*/

						led_state = ~led_state;
						led(led_state);
					}
					// record event
				}

				cum_input[i] = 0;
				last_membrane_write = (uint32_t)cur_t;
			}
			
			// record membrane
			last_integrate = cur_t;
		}

		// generate independent stimulus
		if( (cur_t - last_stim) > stim_test_period ) {
			for(i=0; i<NUM_RBG; i++) {
				if( random() < rbgs[i].rate ) {
					/*cum_input[rbgs[i].dest_row] =*/
						/*lif_accumulate_input(rbgs[i].dest_row,*/
								/*cum_input[rbgs[i].dest_row],*/
								/*weights[rbgs[i].dest_row]);*/
					/*cum_input[0] = lif_accumulate_input(0, cum_input[0], 100);*/
					cum_input[0] = FP(10000.0e-3);
					/*membrane[0] = FP(-20.0e-3);*/
				}
			}
		
			last_stim = cur_t;
		}

		/*t_compute = (t_compute + (get_time_base() - cur_t))/2;*/
	}
}


