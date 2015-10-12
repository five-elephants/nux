#!/bin/sh

OBJCOPY=powerpc-linux-eabi-objcopy

DMEM_LAST_VADDR=0x40003fff
IMEM_LAST_VADDR=0x00003fff

if [ -z "$1" ] && [ -z "$2" ] ; then
	echo "Usage: $0 <ELF file> <binary image basename>"
else
	$OBJCOPY -O binary --remove-section .text --gap-fill 0 --pad-to $DMEM_LAST_VADDR $1 $2_data.raw
	$OBJCOPY -O binary --only-section .text --gap-fill 0 --pad-to $IMEM_LAST_VADDR $1 $2_code.raw
fi

