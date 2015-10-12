// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#include <stdio.h>
#include <pthread.h>
#include <stdint.h>
#include <sched.h>
#include <apr_time.h>
#include <time_base.h>

#define EV_RECORD_SIZE (1000)
#define PRIORITY_HIGH (20)
#define PRIORITY_LOW  (19)

typedef struct {
	uint16_t t_ms;
	uint8_t padding;
	uint8_t id;
} event_t; 

extern void neuron_start();
extern void synarray_start();
extern void synplast_start();
extern void __init_msg(const uint32_t num_ranks, const uint32_t queue_size);
extern void __clear_msg();

extern event_t ev_record[EV_RECORD_SIZE];
extern uint32_t ev_record_end;
extern time_base_t t_compute;
extern time_base_t t_compute_synplast;

//--------------------------------------------------------------------------------

void* neuron_start_wrap(void* arg) 
{ 
	struct sched_param param;
	
	param.sched_priority = PRIORITY_HIGH;
	if( sched_setscheduler(0, SCHED_RR, &param) != 0 )
		perror("sched_setscheduler failed for neuron_start");

	neuron_start();
	return NULL;
}

void* synarray_start_wrap(void* arg)
{
	struct sched_param param;
	
	param.sched_priority = PRIORITY_HIGH;
	if( sched_setscheduler(0, SCHED_RR, &param) != 0 )
		perror("sched_setscheduler failed for synarray_start");

	synarray_start();
	return NULL;
}

void* synplast_start_wrap(void* arg)
{
	struct sched_param param;
	
	param.sched_priority = PRIORITY_LOW;
	if( sched_setscheduler(0, SCHED_RR, &param) != 0 )
		perror("sched_setscheduler failed for synplast_start");

	synplast_start();
	return NULL;	
}

void report_spikes()
{
	int i;

	printf("Events:\n--------------------------------------------------------------------------------\n");
	for(i=0; i<ev_record_end; i++) {
		printf("%6d ms  :  %3d\n",
			ev_record[i].t_ms, ev_record[i].id);
	}
}

void report_t_compute()
{
	printf("Average computing time\n"
		   "   neurons:    %.3f ms\n"
		   "   plasticity: %.3f ms\n",
		(double)t_compute/(double)MS,
		(double)t_compute_synplast/(double)MS);
}

int main()
{
	static const apr_time_t sim_time_ms = 10000;

	apr_time_t t_start;
	apr_time_t elapsed;
	pthread_t neuron_thread;
	pthread_t synarray_thread;
	pthread_t synplast_thread;

	apr_initialize();

	printf("Starting neuroproc simulation...\n");

	/* create queues for two nodes with 16 entries each */
	__init_msg(3, 1024);

	t_start = apr_time_now();

	pthread_create(&neuron_thread, NULL, &neuron_start_wrap, NULL);
	pthread_create(&synarray_thread, NULL, &synarray_start_wrap, NULL);
	pthread_create(&synplast_thread, NULL, &synplast_start_wrap, NULL);

	//pthread_join(neuron_thread, NULL);
	//pthread_join(synarray_thread, NULL);
	
	do {
		printf("\rElapsed: %5d ms", elapsed / 1000);
		apr_sleep(10000);  // sleep 10ms
		elapsed = (apr_time_now() - t_start);
	} while( elapsed < (sim_time_ms * 1000) );

	printf("\n");

	pthread_cancel(neuron_thread);
	pthread_cancel(synarray_thread);
	pthread_cancel(synplast_thread);

	printf("Exiting neurproc simulation\n");

	report_spikes();
	report_t_compute();

	__clear_msg();

	apr_terminate();

	return 0;
}
