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
#include <string.h>
#ifndef TN_TEST_INC
	#include "operators.h"
#else
	#include TN_TEST_INC
#endif

//die maximale kommentarlänge in den dateien betraegt 1024byte

#ifndef TEMP_MEM_AD_FILE
#define TEMP_MEM_AD_FILE "temp_mem_ad.txt"
#endif

#ifndef TN_DUMP_FILE
#define TN_DUMP_FILE "../../../dump_tn_testflow_tn_testflow.mem"
#endif

int cmp_ad(){
	FILE *pFcomp;
	int a, b;
	pFcomp = fopen (TEMP_MEM_AD_FILE,"r");
	fscanf(pFcomp, "%x", &a);
	fclose(pFcomp);
	pFcomp = fopen ("emp_mem_ad.txt","w");
	fprintf(pFcomp, "%d", (a-0x40000000));
	fclose(pFcomp);
	pFcomp = fopen("emp_mem_ad.txt", "r");
	fscanf(pFcomp,"%d", &b);
	fclose(pFcomp);
	return b;
}


void compare(int cmpad){
	int iscomment;	
	int i, indikator;
	char *dump = malloc(1024 + 4*size);
	char *endian = malloc(1024); 
	

	FILE *pFiledump;
	FILE *pFileendian;
	
	pFiledump = fopen (TN_DUMP_FILE,"r");
	if (pFiledump == NULL) {
		printf("error opening file %s \n", TN_DUMP_FILE); 
		exit(1);
	}
 
	pFileendian = fopen ("endianneu.txt","r");
	
	if (pFileendian == NULL) {
		printf("error opening file endinaneu.txt \n"); 
		exit(1);
	}

	i = 0;		
	iscomment = 1;
	do{

		fscanf (pFiledump, "%s", dump);
		if((dump[0] == '/') && (dump[1] == '/')) {
			while(fgetc(pFiledump) != '\n');
			
		} 

		else{
			fseek(pFiledump, (-1)*strlen(dump), SEEK_CUR);
			iscomment = 0;
		}

	}while(iscomment);	



	while(i < cmpad){
		i++;
		printf("%d \n", i);	
		fscanf (pFiledump, "%s", dump);
		
		//ausblendung der kommentare
		if((dump[0] == '/') && (dump[1] == '/')) {
			while(fgetc(pFiledump) != '\n');
			i--;
		} 
		
		else {
			printf("%d, %s \n",i, dump);		
		}
	}
	
	indikator = 1;
	printf("index, s2pp, referenzsystem\n");
	for(i = 0; i < (4*size); i++){
		fscanf(pFiledump, "%s", dump);
		fscanf(pFileendian, "%s", endian);
		
		if(strcmp(dump, endian) != 0){
			printf("%d mismatch in ", i);
			indikator = 0;
		}
		
		printf("%d, %s, %s \n", i, dump, endian);
	}
	
	fclose (pFiledump);
	fclose (pFileendian);

	free(endian);
	free(dump);
	
	if(indikator == 1) printf("match \n");
}
 

int main(){
	//Initialisierung allokierter Bereich wird mit 0 initialisiert
	FILE * pFILE;
//	int* mem = malloc(4*size);
	unsigned char* t;
	int i, j, cmpad;
	for(i=0; i<size; i++){
		mem[i] = 0;
	}
	
	t = mem;
	
	
	
	
	//zu testende Funktion
	test_funktion();
	
	pFILE = fopen ("endianneu.txt","w");	
	
	for(i = 3; i < 4*size; i = i+4){
	
		for(j = i; j > i - 4; j--){
	
			if(t[j] < 0x10){
				//printf("%d, %x, %p, 0%x, %d \n", j, mem[i/4], (mem + (i/4)), t[j], t[j]);
				fprintf(pFILE, "0%x\n", t[j]);
			}
			
			else{
				//printf("%d, %x, %p, %x, %d \n", j, mem[i/4], (mem + (i/4)), t[j], t[j]);
				fprintf(pFILE, "%x\n", t[j]);
			}	
		}
	}

	fclose (pFILE);

//	free(mem);
	cmpad = cmp_ad();
	compare(cmpad);

	return 0;
}	

