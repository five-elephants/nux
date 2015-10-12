#ifndef SPR_H__
#define SPR_H__

#define ATTRIB_UNUSED __attribute__((unused))

#define SPR_SETTER(name, code) \
ATTRIB_UNUSED static void name (const uint32_t v) \
{                                     \
	asm volatile (                      \
      code                            \
			: /* no output */               \
			: "r"(v)  /* input */           \
			: /* clobber */                 \
	);                                  \
}

#define SPR_GETTER(name, code)        \
ATTRIB_UNUSED static uint32_t name () \
{                                     \
	uint32_t rv;                        \
                                      \
	asm volatile (                      \
      code                            \
			: "=r"(rv)  /* output */        \
			: /* no input */                \
			: /* no clobber */              \
	);                                  \
                                      \
	return rv;                          \
}


SPR_GETTER(get_tbu, "mfspr %0, 285")
SPR_GETTER(get_tbl, "mfspr %0, 284")

typedef uint64_t time_base_t;

ATTRIB_UNUSED static time_base_t get_time_base() {
	time_base_t tbu, tbl;
	tbu = get_tbu();
	tbl = get_tbl();
	return (tbu << 32) | tbl;
}

SPR_SETTER(set_dec, "mtdec %0")
SPR_GETTER(get_dec, "mfdec %0")

SPR_SETTER(set_decar, "mtspr 54, %0")
SPR_GETTER(get_decar, "mfspr 54, %0")

#define TCR_DIE (0x04000000)
#define TCR_FIE (0x00800000)
#define TCR_ARE (0x00400000)

SPR_SETTER(set_tcr, "mtspr 340, %0")
SPR_GETTER(get_tcr, "mfspr %0, 340")


#define TSR_DIS (0x08000000)
#define TSR_FIS (0x04000000)

SPR_SETTER(clear_tsr, "mtspr 336, %0")
SPR_GETTER(get_tsr, "mfspr %0, 336")


#define MSR_EE (0x00008000)

SPR_SETTER(set_msr, "mtmsr %0")
SPR_GETTER(get_msr, "mfmsr %0")


	//typedef struct packed {
		//logic[31:20] reserved_2;
		//logic[3:0] gin_sense_level;  //< 1: trigger on level, 0: trigger on edge
		//logic[3:0] gin_trigger;      //< 0: trigger on high level or rising edge
		//logic[3:0] gin_mask;         //< enable pins individually
		//logic[7:1] reserved;
		//logic doorbell_en;           //< enable the doorbell interrupt
	//} Int_ctrl_reg;

#define ICCR_DOORBELL_EN (0x00000001)

SPR_SETTER(set_iccr, "mtspr 0b0001000100, %0")
SPR_GETTER(get_iccr, "mfspr %0, 0b0001000100")

SPR_SETTER(set_srr0, "mtsrr0 %0")
SPR_GETTER(get_srr0, "mfsrr0 %0")
SPR_SETTER(set_srr1, "mtsrr1 %0")
SPR_GETTER(get_srr1, "mfsrr1 %0")

//---------------------------------------------------------------------------

#define TCR_FP_MASK (0x3)
#define TCR_FP_OFF  (24)

#define TCR_FP_BY_256     (0x0)
#define TCR_FP_BY_4096    (0x1)
#define TCR_FP_BY_65536   (0x2)
#define TCR_FP_BY_1048576 (0x3)

#define TCR_FP_BIT_8  (0x0)
#define TCR_FP_BIT_12 (0x1)
#define TCR_FP_BIT_16 (0x2)
#define TCR_FP_BIT_20 (0x3)

ATTRIB_UNUSED static void set_fit_period(uint8_t p)
{
	set_tcr(get_tcr() | ((p	& TCR_FP_MASK) << TCR_FP_OFF));
}

ATTRIB_UNUSED static uint8_t get_fit_period()
{
	return (get_tcr() >> TCR_FP_OFF) & TCR_FP_MASK;
}

//---------------------------------------------------------------------------

/* not needed outside */
#undef SPR_SETTER
#undef SPR_GETTER

#endif

