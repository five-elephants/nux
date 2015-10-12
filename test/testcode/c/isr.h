#ifndef ISR_H__
#define ISR_H__

/** Code fragment with comments for the isr pro- and epilogue */
// XXX save/restore CTR, XER, ... ?
// asm (
// 	".global isr_dec\n"
// 	"isr_dec:\n"
// 	"	stw 0, -32*4(1)\n"    // save GPR0
// 	"	mflr 0\n"             // get link register
// 	"	stwu 1, -34*4(1)\n"   // save back chain word
// 	"	stw 0, +35*4(1)\n"    // save link register
// 	
// 	"	mfcr 0\n"
// 	"	stw 0, 3*4(1)\n"      // store CR
// 	"	stmw 2, 4*4(1)\n"     // store GPRs
// 
// 	"	bl isr_dec_func\n"    // call actual service routine
// 
// 	"	lwz 0, +35*4(1)\n"    // load saved link register
// 	"	mtlr 0\n"             // restore link register
// 	"	lmw 2, 4*4(1)\n"      // restore GPRs
// 	"	lwz 0, +3*4(1)\n"     // load saved CR
// 	"	mtcr 0\n"             // restore CR
// 	"	lwz 0, +2*4(1)\n"     // restore GPR0
// 	"	addi 1, 1, 34*4\n"    // remove frame from stack
// 
// 	"	rfi\n"                // return from interrupt
// );

/** Prologue code for interrupt service routines.
 * Saves all GPRs and the CR. Creates a new stack frame on top of the user 
 * stack. */
#define ISR_PROLOGUE \
	"	stw 0, -32*4(1)\n"    \
	"	mflr 0\n"             \
	"	stwu 1, -34*4(1)\n"   \
	"	stw 0, +35*4(1)\n"    \
	"	mfcr 0\n"             \
	"	stw 0, 3*4(1)\n"      \
	"	stmw 2, 4*4(1)\n"     

/** Epilogue for interrupt service routines.
 * Restores environment and pops stack frame before returning from the 
 * interrupt */
#define ISR_EPILOGUE \
	"	lwz 0, +35*4(1)\n"    \
	"	mtlr 0\n"             \
	"	lmw 2, 4*4(1)\n"      \
	"	lwz 0, +3*4(1)\n"     \
	"	mtcr 0\n"             \
	"	lwz 0, +2*4(1)\n"     \
	"	addi 1, 1, 34*4\n"    \
                              \
	"	rfi\n"                

/** Shell code macro for the decrementer interrupt service routine. */
#define ISR_DEC \
asm (                         \
	".global isr_dec\n"       \
	"isr_dec:\n"              \
ISR_PROLOGUE                  \
	"	bl isr_dec_func\n"    \
ISR_EPILOGUE                  \
);                            \
                              \
void isr_dec_func()

/** Shell code macro for the fixed interval timer interrupt service routine. */
#define ISR_FIT \
asm (                         \
	".global isr_fit\n"       \
	"isr_fit:\n"              \
ISR_PROLOGUE                  \
	"	bl isr_fit_func\n"    \
ISR_EPILOGUE                  \
);                            \
                              \
void isr_fit_func()

/** Shell code macro for the doorbell interrupt service routine. */
#define ISR_DOORBELL \
asm (                            \
	".global isr_doorbell\n"     \
	"isr_doorbell:\n"            \
ISR_PROLOGUE                     \
	"	bl isr_doorbell_func\n"  \
ISR_EPILOGUE                     \
);                               \
                                 \
void isr_doorbell_func()


#endif

