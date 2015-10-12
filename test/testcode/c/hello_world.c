// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.



void start();
void hello_world();
void mem_set(int* a, int n, int value);
void vector_add(int* res, int* a, int* b, int length);

void start()
{
	hello_world();
}

void hello_world()
{
	const int length = 10;
	int* a = 0;
	int* b = length * sizeof(int);
	int* res = 2*length * sizeof(int);
	int i;

	for(i=0; i<length; i++)
		a[i] = i;

	mem_set(b, length, 1);
	vector_add(res, a, b, length);
}

void mem_set(int* a, int n, int value)
{
	int i;

	for(i=0; i<n; ++i)
		a[i] = value;
}

void vector_add(int* res, int* a, int *b, int length)
{
	int i;

	for(i=0; i<length; ++i)
		res[i] = a[i] + b[i];
}
