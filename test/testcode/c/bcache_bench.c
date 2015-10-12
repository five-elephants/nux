// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



/** This is a random number generator called multiply with carry (MWC) as
 * proposed by George Marsaglia. */
unsigned int random()
{
	static unsigned int z = 521288629;
	static unsigned int w = 362436069;

	z = 36969 * (z & 65535) + (z >> 16);
	w = 18000 * (w & 65535) + (w >> 16);
	return (z << 16) + w;
}


void vector_madd_asm(int *res, int *a, int *b, int *c, unsigned int length)
{
#define BLOCK_LEN 8
#define EXPR(x) (a[x] * b[x] + c[x])

	unsigned int i, j;
	unsigned int num_blocks = length / BLOCK_LEN;
	unsigned int rem = length % BLOCK_LEN;

	i = 0;
	/*for(i=0; i<num_blocks*BLOCK_LEN; i += BLOCK_LEN) {*/
		asm(
			"li 9, 0\n"  // init loop counter
			"vector_madd_asm_loop:\n"
			"addi 9, 9, 8\n"  // loop increment

			// load four operands from a
			"lwz 20, 0(%0)\n"
			"lwz 21, 4(%0)\n"
			"lwz 22, 8(%0)\n"
			"lwz 23, 12(%0)\n"

			// load four operands from b
			"lwz 24, 0(%1)\n"
			"lwz 25, 4(%1)\n"
			"lwz 26, 8(%1)\n"
			"lwz 27, 12(%1)\n"

			"cmplw 7, 9, %4\n"  // loop check

			// load four operands from c
			"lwz 28, 0(%2)\n"
			"lwz 29, 4(%2)\n"
			"lwz 30, 8(%2)\n"
			"lwz 31, 12(%2)\n"

			// start multiplication and load the next operand from a and b
			"mullw 16, 20, 24\n"
			"mullw 17, 21, 25\n"
			"mullw 18, 22, 26\n"
			"mullw 19, 23, 27\n"

			"lwz 20, 16(%0)\n"
			"lwz 24, 16(%1)\n"
			"lwz 21, 20(%0)\n"
			"lwz 25, 20(%1)\n"
			"lwz 22, 24(%0)\n"
			"lwz 26, 24(%1)\n"
			"lwz 23, 28(%0)\n"
			"lwz 27, 28(%1)\n"

			// add the first four operands
			"add 16, 16, 28\n"
			"add 17, 17, 29\n"
			"add 18, 18, 30\n"
			"add 19, 19, 31\n"

			// start multiplication of the next four operands
			"mullw 11, 20, 24\n"
			"mullw 12, 21, 25\n"
			"mullw 14, 22, 26\n"
			"mullw 15, 23, 27\n"

			"lwz 28, 0(%2)\n"
			"lwz 29, 4(%2)\n"
			"lwz 30, 8(%2)\n"
			"lwz 31, 12(%2)\n"

			"stw 16, 0(%3)\n"
			"stw 17, 4(%3)\n"
			"stw 18, 8(%3)\n"
			"stw 19, 12(%3)\n"

			// add the next four operands
			"add 16, 11, 28\n"
			"add 17, 12, 29\n"
			"add 18, 14, 30\n"
			"add 19, 15, 31\n"

			// store next four operands
			"stw 16, 0(%3)\n"
			"stw 17, 4(%3)\n"
			"stw 18, 8(%3)\n"
			"stw 19, 12(%3)\n"

			"blt 7, vector_madd_asm_loop\n"  // loop branch
			
			: 
			: "r"(a), "r"(b), "r"(c), "r"(i), "r"(num_blocks * BLOCK_LEN)
			: "9","11","12","14","15","16","17","18","19","20","21","22","23","24","25","26","27","28","29","30","31"
		);
	/*}*/
		
	for(j=0; j<rem; j++)
		res[i+j] = EXPR(i+j); 

#undef EXPR
#undef BLOCK_LEN
}

/** Calculate res[i] = a[i] * b[i] + c[i] */
void vector_madd(int *res, int *a, int *b, int *c, unsigned int length)
{
	/*unsigned int i;*/
	/*for(i=0; i<length; i++) {*/
		/*res[i] = a[i] * b[i] + c[i];*/
	/*}*/
#define BLOCK_LEN 4
#define EXPR(x) (a[x] * b[x] + c[x])

	unsigned int i, j;
	unsigned int num_blocks = length / BLOCK_LEN;
	unsigned int rem = length % BLOCK_LEN;

	for(i=0; i<num_blocks*BLOCK_LEN; i += BLOCK_LEN) {
		/*for(j=0; j<BLOCK_LEN; j++)*/
			/*v[i+j] = val;*/
		res[i+0] = EXPR(i+0); 
		res[i+1] = EXPR(i+1); 
		res[i+2] = EXPR(i+2); 
		res[i+3] = EXPR(i+3); 
#if BLOCK_LEN > 4
		res[i+4] = EXPR(i+4); 
		res[i+5] = EXPR(i+5); 
		res[i+6] = EXPR(i+6); 
		res[i+7] = EXPR(i+7); 

#if BLOCK_LEN > 8
		res[i+8]  = EXPR(i+8);
		res[i+9]  = EXPR(i+9);
		res[i+10] = EXPR(i+10);
		res[i+11] = EXPR(i+11);
		res[i+12] = EXPR(i+12);
		res[i+13] = EXPR(i+13);
		res[i+14] = EXPR(i+14);
		res[i+15] = EXPR(i+15);
#endif /* BLOCK_LEN > 8 */
#endif /* BLOCK_LEN > 4 */
	}
		
	for(j=0; j<rem; j++)
		res[i+j] = EXPR(i+j); 

#undef EXPR
#undef BLOCK_LEN
}

void rinit_vector(int *v, unsigned int length)
{
	unsigned int i;
	for(i=0; i<length; i++) {
		v[i] = random();
	}
}


void vector_set(int *v, unsigned int val, unsigned int length)
{
#define BLOCK_LEN 16 

	unsigned int i, j;
	unsigned int num_blocks = length / BLOCK_LEN;
	unsigned int rem = length % BLOCK_LEN;

	for(i=0; i<num_blocks*BLOCK_LEN; i += BLOCK_LEN) {
		/*for(j=0; j<BLOCK_LEN; j++)*/
			/*v[i+j] = val;*/
		v[i+0] = val;
		v[i+1] = val;
		v[i+2] = val;
		v[i+3] = val;
#if BLOCK_LEN > 4
		v[i+4] = val;
		v[i+5] = val;
		v[i+6] = val;
		v[i+7] = val;

#if BLOCK_LEN > 8
		v[i+8] = val;
		v[i+9] = val;
		v[i+10] = val;
		v[i+11] = val;
		v[i+12] = val;
		v[i+13] = val;
		v[i+14] = val;
		v[i+15] = val;
#endif /* BLOCK_LEN > 8 */
#endif /* BLOCK_LEN > 4 */
	}
		
	for(j=0; j<rem; j++)
		v[i+j] = val;

#undef BLOCK_LEN
}

void bench_madd()
{
	const static unsigned int size = 256;

	int i, j;
	int a[size];
	int b[size];
	int c[size];
	int res[size];

	for(i=0; i<40; i++) {
		/*rinit_vector(a, size);*/
		/*rinit_vector(b, size);*/
		/*rinit_vector(c, size);*/
		vector_set(a, random(), size);
		vector_set(b, random(), size);
		vector_set(c, random(), size);

		/*vector_madd(res, a, b, c, size);*/
		for(j=0;j<20; j++)
			vector_madd_asm(res, a, b, c, size);
			/*vector_madd(res, a, b, c, size);*/
	}
}

void bench_random()
{
	const static unsigned int iterations = 1;
	const static unsigned int size = 64;

	int i, j;
	int data[size];

	for(j=0; j<iterations; j++) {
		for(i=0; i<size; i++) {
			rinit_vector(data, size);
		}
	}
}

void start()
{
	bench_madd();
	/*bench_random();*/
}
