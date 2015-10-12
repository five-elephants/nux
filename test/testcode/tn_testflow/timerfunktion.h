/******************************************************
timerfunktion.h
time_base_t defined as variable type of timeregister (64bit)
get_time_base() to get the timevalue of the moment
time_measured as global variable to perform time_readout
***************************************************************/

#define GET_TBU(x) asm volatile("mfspr %0, 285" : "=r"(x) ::)
#define GET_TBL(x) asm volatile("mfspr %0, 284" : "=r"(x) ::)
#define TICKS_PER_SEC (100000000)  



typedef unsigned int uint32_t;
typedef unsigned long long int uint64_t;
typedef uint64_t time_base_t;

time_base_t time_measured;

uint32_t get_tbu(){
	uint32_t tbu;

	asm volatile("mfspr %0, 285"
			: "=r"(tbu)  /* output */
			: /* no input */
			: /* no clobber */);

	return tbu;
}


uint32_t get_tbl(){

	uint32_t tbl;

	asm volatile("mfspr %0, 284"
			: "=r"(tbl)  /* output */
			: /* no input */
			: /* no clobber */);

	return tbl;
}


time_base_t get_time_base(){

	uint64_t tbu, tbl;
	time_base_t rv;

	tbu = get_tbu();
	tbl = get_tbl();

	rv = (tbu << 32) | tbl;
//	time_measured = rv;
	return rv;
}
