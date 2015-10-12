/****************************************************** 
timerfunktion.h 
time_base_t defined as variable type of timeregister (64bit) 
get_time_base() to get the timevalue of the moment 
time_measured as global variable to perform time_readout 
***************************************************************/ 
#include "timerfunktion.h" 
#define size 128  
#define cycles 15
#include "maybe_useful/seed/c32-20.h" 
#include "maybe_useful/seed/w32-20.h" 
unsigned int mem[size]; 

void test_funktion(){ 
	
	unsigned int andl[8] = {0xf, 0xf0, 0xf00, 0xf000, 0xf0000, 0xf00000, 0xf000000, 0xf0000000};
	unsigned int ands[8] = {3, 12, 48, 192, 768, 3072, 12288, 49152};
	unsigned int k;
	int i, j, l;
	unsigned int temp[8];
	unsigned int stemp[8];	
	time_base_t time0, time1;	
		
	unsigned int g01[16] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};
	unsigned int g10[16] = {15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0};
	unsigned int g11[16] = {12, 11, 13, 10, 14, 9, 15, 8, 0, 7, 1, 6, 2, 5, 3, 4};

	time0 = get_time_base();
	for(l=0; l<cycles; l++){
		for(i=0; i<size; i++){
//			printf("%d, %x, %x\n", i, weight[i], correlation[i]);
			for(j=0; j<7; j++){
				stemp[j] = (correlation[i] & ands[j]) >> (j*2);
				temp[j] = ((weight[i] & andl[j]) >> (j*4));
			}
			stemp[7] = (correlation[i] >> 14);
			temp[7] = (weight[i] >> 28);
			
			for(j=0; j<8; j++){
			//	printf("%x, %x \n", temp[j], stemp[j]);
				if(stemp[j] == 0) k = temp[j];
				else if(stemp[j] == 1) k = g01[temp[j]];
				else if(stemp[j] == 2) k = g10[temp[j]];
				else if(stemp[j] == 3) k = g11[temp[j]];
			//	else {printf("error\n");}
			//	mem[(i*8)+j] = k;
				mem[i] = ((mem[i] << 4) | k);
			}
			
		}
	}
	time1 = get_time_base();
	time_measured = time1 - time0;

}
