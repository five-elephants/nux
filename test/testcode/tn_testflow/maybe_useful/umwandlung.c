// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#include<stdio.h>

#define size 1024

#include "seed/weight20.h"
#include "seed/correlation20.h"


int main(){
	int i, j;
	int z = 0;
	unsigned int weight[size/4];
	unsigned int temp = 0;
	unsigned short int stemp = 0;
	unsigned short int correlation[size/4];
	
	FILE *pFile1, *pFile2;

	pFile1 = fopen("w32-20.h", "w");
	pFile2 = fopen("c32-20.h", "w");

	fprintf(pFile1, "volatile unsigned int weight[size] = {");
	fprintf(pFile2, "volatile unsigned short int correlation[size] = {");

	for(i=0; i<(size/4); i++){
		weight[i] = 0;
		correlation[i] = 0;
	}
/*
	printf("%x\n", einc[0]);
	weight[0] = einc[0] << 4;
	printf("%x\n", weight[0]);

*/

	for(j=0; z<size; j++){
		for(i=0; i<8; i++){
			temp = (weight[j] << 4);
			weight[j] = temp + eing[z+i];
//			printf("%x\n", weight[j]);
		}
		z=z+8;
	}

	z = 0;	
	for(j=0; z<size; j++){
		for(i=0; i<8; i++){
			stemp = (correlation[j] << 2);
			correlation[j] = stemp + einc[z+i];
//			printf("%x\n", correlation[j]);
		}
		z=z+8;
	}
	
	for(i=0; i<size/8; i++){
		fprintf(pFile1, "%uu", weight[i]);
		if(i!=((size/8)-1)) fprintf(pFile1, ", ");
		printf("%x\n", weight[i]);
	}

	for(i=0; i<size/8; i++){
		fprintf(pFile2, "%uu", correlation[i]);
		if(i!=((size/8)-1)) fprintf(pFile2, ", ");
		printf("%x\n", correlation[i]);
	}

	fprintf(pFile1, "};");
	fprintf(pFile2, "};");

	fclose(pFile1);
	fclose(pFile2);
return 0;
}
