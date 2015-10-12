#ifndef S2PP_TIME_BASE_H__
#define S2PP_TIME_BASE_H__

/*#define SIMULATION*/

#ifdef SIMULATION
#	define MS (1)
#else
#	define MS (100000)
#endif  /* SIMULATION */

#define GET_TBU(x) asm volatile("mfspr %0, 285" : "=r"(x) ::)
#define GET_TBL(x) asm volatile("mfspr %0, 284" : "=r"(x) ::)

//typedef uint64_t time_base_t;

//static time_base_t get_time_base()
//{
	//uint32_t tbu, tbl;
	//time_base_t rv;

	//GET_TBU(tbu);
	//GET_TBL(tbl);

	//rv = ( (uint64_t)(tbu) << 32 ) | (uint64_t)tbl;   // how does this look in assembler?

	//return rv;
//}

static uint16_t millisecond_16()
{
	uint32_t tbl;

	GET_TBL(tbl);

	return (uint16_t)(tbl / MS);
}

#endif

