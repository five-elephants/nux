/******************************************************
timerfunktion.h
time_base_t defined as variable type of timeregister (64bit)
get_time_base() to get the timevalue of the moment
time_measured as global variable to perform time_readout
***************************************************************/
//#include "timerfunktion.h"

//anzahl der ints mit denen der allokierte speicher befuellt werden soll
#define size 44
int mem[size];

void test_funktion(){

	int i, j, x;
//	time_base_t time0, time1;

	j = 0;	
	
//	time0 = get_time_base();	

	for(x = 3; x < 200; x++){

		i = 2;

		while(x%i != 0){
			i++;
		}
		
		if(x == i){
			mem[j] = x;

			j++;
		}
	}
	
//	time1 = get_time_base();
	
//	time_measured = time1 - time0;	


/*	
	//testlaeufe
	//Fuellung des Arrays mit ints
	for(i=0; i < 2048; i++) {
		mem[i] = i;
	}
*/


}
