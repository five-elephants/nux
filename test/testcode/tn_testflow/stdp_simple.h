/******************************************************
timerfunktion.h
time_base_t defined as variable type of timeregister (64bit)
get_time_base() to get the timevalue of the moment
time_measured as global variable to perform time_readout
***************************************************************/
#include "timerfunktion.h"

#define size 1024
#define cycles 15
#include "seed/correlation1.h"
#include "seed/weight1.h" 
int mem[size];


void test_funktion(){
	unsigned char k;
	int i, j;	
	time_base_t time0, time1;	
	
//	for(i=0; i<size; i++) k[i] = 0;

	unsigned char g01[16] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};
	unsigned char g10[16] = {15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0};
	unsigned char g11[16] = {12, 11, 13, 10, 14, 9, 15, 8, 0, 7, 1, 6, 2, 5, 3, 4};
	
	time0 = get_time_base();
	for(j=0; j<cycles; j++){
		for(i=0; i<size; i++){
			while(einc[i] == 0) i++;
			if(einc[i] == 1) k = g01[eing[i]];
			if(einc[i] == 2) k = g10[eing[i]];
			if(einc[i] == 3) k = g11[eing[i]];
			mem[i] = k;
		}
	}	
	time1 = get_time_base();

//	for(i=0; i<size; i++) mem[i] = k[i];

	time_measured = time1 - time0;
}
