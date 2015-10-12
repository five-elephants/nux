#!/bin/sh

# path to GNU assembler for target powerpc-common-linux or propably powerpc-*-*
#ASM=/home/simon/src/binutils-2.20/gas/as-new
#ASM=/opt/s2pp/bin/powerpc-linux-eabi-as
ASM="powerpc-linux-eabi-as -many"

if [ $# -eq 0 ] ; then
	echo "Usage: $0 <source file> <mem file>"
	echo
	echo "$0 compiles assembler files for use with the modelsim simulator."
	echo "The produced memory file can be loaded to instruction memory using 'mem load'"
	exit 1
fi

if [ -f a.out ] ; then
	echo "There is a file a.out which would be overwritten by this file. Please remove it. Thanks."
	echo "Aborting."
	exit 1
fi

# SED_EXPR_1='s/^\(.*\)\([0-9A-F]\{8\}\)\(.*\)/\2/g'
# SED_EXPR_2='/^\(.*\)\([0-9]\{2,4\}\)\([ \t]\+\)$/d'
# SED_EXPR_3='/^\(.*\)\([0-9]\{2,4\}\)\(.*:.*\)$/d'

echo "// format=hex addressradix=h dataradix=h version=1.0 wordsperline=1" > $2
#$ASM -al $1 | sed -e '1,4d' | sed -e "$SED_EXPR_1" -e "$SED_EXPR_2" -e "$SED_EXPR_3" >> $2
$ASM -al $1 | awk -F" " '{print $3}' | sed -e '/^[0-9A-F]\{8\}/!d' >> $2
rm a.out
