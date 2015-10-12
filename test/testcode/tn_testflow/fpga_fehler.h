/****************************************************** 
timerfunktion.h 
time_base_t defined as variable type of timeregister (64bit) 
get_time_base() to get the timevalue of the moment 
time_measured as global variable to perform time_readout 
***************************************************************/ 
//#include "timerfunktion.h" 
#define size 128  
#define cycles 1 
#include "seed/c32-1.h" 
#include "seed/w32-1.h" 
int mem[8*size]; 

void test_funktion(){ 
	
	unsigned int andl[8] = {0xf, 0xf0, 0xf00, 0xf000, 0xf0000, 0xf00000, 0xf000000, 0xf0000000};
	unsigned int ands[8] = {3, 12, 48, 192, 768, 3072, 12288, 49152};
	unsigned int k, n, m;
	int i, j, l;
	unsigned int temp[8];
	unsigned int stemp[9];	
//	time_base_t time0, time1;	
		
	unsigned int g01[16] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};
	unsigned int g10[16] = {15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0};
	unsigned int g11[16] = {12, 11, 13, 10, 14, 9, 15, 8, 0, 7, 1, 6, 2, 5, 3, 4};

//	time0 = get_time_base();
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
//				printf("%x, %x \n", temp[j], stemp[j]);
				if(stemp[j] == 0) k = temp[j];
				else if(stemp[j] == 1) {m = temp[j]; k = g01[m];}
				else if(stemp[j] == 2) {m = temp[j]; k = g10[m];}
				else if(stemp[j] == 3) {m = temp[j]; k = g11[m];}
			//	else {printf("error\n");}
			//	mem[(i*8)+(j*2)] = k;
				mem[(i*8)+j] = k;
			//	mem[(i*8)+(j*2)+1] = 15;
			//	mem[(i*8)+3*j] = k;
			//	mem[(i*8)+3*j+1] = temp[j];
			//	mem[(i*8)+3*j+2] = stemp[j];
			}
			
		}
	}
//	time1 = get_time_base();
//	time_measured = time1 - time0;

}
