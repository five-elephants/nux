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
#include <stdlib.h>

#define size 1024


int main (){
	
	int i, corr, weight;
	FILE *pCORR, *pWEIGHT;
	unsigned int seed[20] = {802, 914, 694, 313, 1337, 156, 144, 12, 1848, 1776, 1983, 1923, 61, 5883, 270707, 280807, 100783, 2509, 7588, 110811};	

	pCORR = fopen("seed/correlation20.h","w");
	pWEIGHT = fopen("seed/weight20.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[0]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation19.h","w");
	pWEIGHT = fopen("seed/weight19.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[1]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation18.h","w");
	pWEIGHT = fopen("seed/weight18.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[2]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation17.h","w");
	pWEIGHT = fopen("seed/weight17.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[3]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation16.h","w");
	pWEIGHT = fopen("seed/weight16.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[4]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation15.h","w");
	pWEIGHT = fopen("seed/weight15.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[5]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation14.h","w");
	pWEIGHT = fopen("seed/weight14.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[6]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation13.h","w");
	pWEIGHT = fopen("seed/weight13.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[7]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation12.h","w");
	pWEIGHT = fopen("seed/weight12.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[8]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation11.h","w");
	pWEIGHT = fopen("seed/weight11.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[9]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation10.h","w");
	pWEIGHT = fopen("seed/weight10.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[10]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation9.h","w");
	pWEIGHT = fopen("seed/weight9.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[11]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation8.h","w");
	pWEIGHT = fopen("seed/weight8.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[12]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation7.h","w");
	pWEIGHT = fopen("seed/weight7.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[13]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation6.h","w");
	pWEIGHT = fopen("seed/weight6.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[14]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation5.h","w");
	pWEIGHT = fopen("seed/weight5.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[15]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation4.h","w");
	pWEIGHT = fopen("seed/weight4.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[16]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation3.h","w");
	pWEIGHT = fopen("seed/weight3.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[17]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);


	pCORR = fopen("seed/correlation2.h","w");
	pWEIGHT = fopen("seed/weight2.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[18]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);

	pCORR = fopen("seed/correlation1.h","w");
	pWEIGHT = fopen("seed/weight1.h","w");

	fprintf(pCORR,"volatile unsigned char einc[size] = {");
	fprintf(pWEIGHT, "volatile unsigned char eing[size] = {");
	
	for(i=0; i<size; i++){
		srand (seed[19]+i);
		corr = rand() % 4;
		weight = rand() % 16;
		printf ("%d, Korrelationsbit: %d, Gewicht: %d\n", i, corr, weight);
		fprintf(pCORR, "%d", corr);
		fprintf(pWEIGHT, "%d", weight);
		if(i != (size-1)) fprintf(pCORR,", ");
		if(i != (size-1)) fprintf(pWEIGHT, ", ", weight);
	}

	fprintf(pCORR, "};\n");
	fprintf(pWEIGHT, "};\n");
	fclose(pCORR);
	fclose(pWEIGHT);


	
return 0;
}
