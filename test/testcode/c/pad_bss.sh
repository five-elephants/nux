SIZE=`powerpc-linux-eabi-objdump $1 -h|grep -w '.bss'|awk --non-decimal-data '{print ("0x"$3)+0}'`

if [ "$SIZE" != "" ] ; then
	for (( i = 0 ; i < $SIZE ; i++ ))
	do
		i_inc=`expr $i + 1`
		tmp=`expr $i_inc % 4`
		if [ $tmp == 0 ] 
		then
			echo "00 " >> $2
		else
			echo -n "00 " >> $2 
		fi
	done
fi


SIZE=`powerpc-linux-eabi-objdump $1 -h|grep -w '.sbss'|awk --non-decimal-data '{print ("0x"$3)+0}'`
if [ "$SIZE" != "" ] ; then
	for (( i = 0 ; i < $SIZE ; i++ ))
	do
		i_inc=`expr $i + 1`
		tmp=`expr $i_inc % 4`
		if [ $tmp == 0 ] 
		then
			echo "00 " >> $2
		else
			echo -n "00 " >> $2 
		fi
	done
fi
