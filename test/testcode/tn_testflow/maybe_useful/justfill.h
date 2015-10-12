/******************************************************
timerfunktion.h
time_base_t defined as variable type of timeregister (64bit)
get_time_base() to get the timevalue of the moment
time_measured as global variable to perform time_readout
***************************************************************/
#include "timerfunktion.h"

#define size 1499

int mem[size];

void test_funktion(){
	int i;
	time_base_t time0, time1;

	time0 = get_time_base();

	for(i=0; i<size; i++){
		mem[i] = i;
	}

	time1 = get_time_base();
	time_measured = time1 - time0;


}

