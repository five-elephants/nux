// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


typedef unsigned char uint8_t;
typedef unsigned int uint32_t;

#define SIZE (3000)

uint32_t v[SIZE];
uint32_t u[SIZE];

static void init()
{
	int i;
	for(i=0; i<SIZE; i++) {
		v[i] = 0;
		u[i] = 0;
	}
}

static void fill()
{
	int i;

	v[0] = 0;
	for(i=1; i<SIZE; i++)
		v[i] = v[i-1] + 1;
}

static void forever()
{
	while(1) {
		asm volatile ("nop");
	}
}

static void forever_burn()
{
	int i;

	while( 1 ) {
		for(i=1; i<SIZE; i++) {
			/*u[i] = ((u[i-1] * u[i]) / v[i]) + v[i];	*/
			u[i] = (u[i-1] * u[i]) + v[i];	
		}
	}
}

void start()
{
	init();
	fill();
	/*forever_burn();*/
}
