#!/bin/sh

A=`mktemp`
B=`mktemp`

xxd $1 > $A
xxd $2 > $B
vimdiff $A $B

rm $A
rm $B
