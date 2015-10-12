#ifndef LINUX_TIME_BASE_H__
#define LINUX_TIME_BASE_H__

#include <stddef.h>
#include <time.h>
#include <sys/time.h>

/*#define SIMULATION*/

#ifdef SIMULATION
#	define MS (1)
#else
//#	define MS (100000)
#	define MS (10)
#endif  /* SIMULATION */

#define GET_TBU(x) (x = get_tb_f(1))
#define GET_TBL(x) (x = get_tb_f(0))

typedef uint64_t time_base_t;

static time_base_t get_time_base()
{
	struct timeval tv;
	time_base_t tb;
	//struct tm tm_zero = { 
		//.tm_sec = 0,
		//.tm_min = 0,
		//.tm_hour = 0,
		//.tm_mday = 1,
		//.tm_mon = 1,
		//.tm_year = 2011,
		//.tm_wday = 0,
		//.tm_yday = 0,
		//.tm_isdst = 0
	//};
	//time_t t_zero = mktime(&tm_zero);
	time_t t_zero = 1325886795ul;

	gettimeofday(&tv, NULL);

	tb = (tv.tv_sec - t_zero) * 1000 * MS;
	tb += (tv.tv_usec * MS) / 1000;

	return tb;
}

static uint32_t get_tb_f(int upper)
{
	//struct timeval tv;
	//uint64_t tb;

	//gettimeofday(&tv, NULL);

	//tb = (tv.tv_sec - t_zero) * 1000 * MS;
	//tb += tv.tv_usec * (MS / 1000);
	
	time_base_t tb = get_time_base();

	if( upper ) {
		return (tb & 0xffffffff00000000ul) >> 32;
	} else {
		return tb & 0xfffffffful;
	}
}

static uint16_t millisecond_16()
{
	uint32_t tbl;

	GET_TBL(tbl);

	return (uint16_t)(tbl / MS);
}

#endif
