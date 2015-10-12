// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <apr_pools.h>
#include <apr_queue.h>

#include <msg_map.h>

typedef struct {
	uint32_t rank;
	uint32_t addr;
	apr_queue_t* queue;
} addr_map_t;
//--------------------------------------------------------------------------------

static uint32_t num_ranks;
static uint32_t num_queues;
static uint32_t queue_size;
static uint32_t addr_map_size;

static apr_pool_t* mem_pool;
static apr_queue_t** queues;
static addr_map_t* addr_map;

//--------------------------------------------------------------------------------
static apr_queue_t* get_queue(const uint32_t rank, const uint32_t addr)
{
	unsigned int i;

	for(i=0; i<addr_map_size; i++) {
		if( (addr_map[i].rank == rank)
			&& (addr_map[i].addr == addr) )
		{
			return addr_map[i].queue;
		}
	}

	return NULL;
}
//--------------------------------------------------------------------------------
void __send_msg(const uint32_t rank, const uint32_t addr, const uint32_t data)
{
	apr_queue_t* q;
	uint32_t* tmp;

	/*printf("[%d]    >>  Sending to addr=0x%08x with data = 0x%08x\n",
		rank, addr, data);*/

	q = get_queue(rank, addr);

	/* allocate temporary storage for message */
	tmp = (uint32_t*) malloc(sizeof(uint32_t));
	*tmp = data;

	apr_queue_push(q, (void*)tmp);
}

uint32_t __recv_msg(const uint32_t rank, const uint32_t addr)
{
	void* res;
	apr_queue_t* q;
	uint32_t rv;

	/*printf("[%d]  <<    Receiving from addr=0x%08x\n",
		rank, addr);*/

	q = get_queue(rank, addr);
	apr_queue_pop(q, &res);

	rv = *((uint32_t*)res);
	free((uint32_t*)res);

	return rv;
}

uint32_t __msg_waiting(const uint32_t rank, uint32_t addr)
{
	apr_queue_t* q;

	q = get_queue(rank, addr);
	if( apr_queue_size(q) > 0 )  // XXX not thread safe -> maybe not correct to use this
		return 1;
	else 
		return 0;
}
//--------------------------------------------------------------------------------

void __init_msg(const uint32_t _num_ranks, const uint32_t _queue_size)
{
	int i, j, k;
	int queue_index;
	uint32_t addr_in, addr_out;
	apr_queue_t* tmp_queue;
	apr_status_t stat;
	char buf[256];

	num_ranks = _num_ranks;
	num_queues = num_ranks * (num_ranks - 1);
	queue_size = _queue_size;
	addr_map_size = 2*num_queues;

	printf("Going to allocate %d queues and %d address map entries.\n",
		num_queues, addr_map_size);

	/* allocate memory for queue pointers */
	apr_pool_create(&mem_pool, NULL);
	queues = (apr_queue_t**)apr_palloc(mem_pool, sizeof(apr_queue_t*)*num_queues);

	for(i=0; i<num_queues; i++) {
		if( (stat = apr_queue_create(&tmp_queue, queue_size, mem_pool)) != APR_SUCCESS ) {
			apr_strerror(stat, buf, 256);
			printf("ERROR[APR]: '%s'", buf);
			exit(1);
		}
		queues[i] = tmp_queue;
		/*apr_queue_create(&(queues[i]), queue_size, mem_pool);*/
	}

	/* create address map */
	addr_map = (addr_map_t*) apr_palloc(mem_pool, sizeof(addr_map_t)*addr_map_size);

	//addr_map[0] = (addr_map_t) { .rank = 0, .addr = MSG_IN_A, .queue = queues[0] };
	//addr_map[1] = (addr_map_t) { .rank = 0, .addr = MSG_OUT_A, .queue = queues[1] };
	//addr_map[2] = (addr_map_t) { .rank = 1, .addr = MSG_IN_A, .queue = queues[1] };
	//addr_map[3] = (addr_map_t) { .rank = 1, .addr = MSG_OUT_A, .queue = queues[0] };

	k = 0;
	for(i=0; i<num_ranks; i++) {
		addr_in = MSG_IN_A;
		addr_out = MSG_OUT_A;
		for(j=0; j<num_ranks; j++) {
			if( j != i ) {
				addr_map[2*k] = (addr_map_t) { 
					.rank = i,
					.addr = addr_out,
					.queue = queues[k]
				};

				printf("(i=%d, j=%d, k=%d) out at addr 0x%08x and queue_index = %d\n",
					i, j, k, addr_out, k);

				queue_index = j*(num_ranks-1) + ( (i<j)?i:(i-1) );
				addr_map[2*k+1] = (addr_map_t) {
					.rank = i,
					.addr = addr_in,
					.queue = queues[queue_index]
				};

				printf("(i=%d, j=%d, k=%d) in at addr 0x%08x and queue_index = %d\n",
					i, j, k, addr_in, queue_index);

				++k;
				addr_in += MSG_IN_STEP;
				addr_out += MSG_OUT_STEP;
			}
		}
	}
}

void __clear_msg()
{
	apr_pool_destroy(mem_pool);
}
//--------------------------------------------------------------------------------


