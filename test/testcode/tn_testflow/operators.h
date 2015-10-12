int size = 35;
int mem[35];

int zeiger_funktion(int a){
	int *zeiger;
	zeiger = &a;
	return *zeiger;
}

int umwandlung_funktion(){
	float f = 1.5;
	int i = (int)f;
	float a = 5;
	int b = 2;
	float ergebnis;
	ergebnis = a / (float)b;
	return ergebnis;
}

int dereferenzierung_funktion(int a, int b){
	int *zeiger;
	zeiger = &a;
	*zeiger = b;
	return a;
}

int shift_funktion1(int var, int shift){
	return (var << shift);
}

int shift_funktion2(int var, int shift){
	return (var >> shift);
}

int shift_funktion3(int var, int shift){
	int erg;
	erg = (var << shift);
	return erg;
}

int bitnot_funktion(int var){
	return (~var);
}

int bitxor_funktion(int var1, int var2){
	int erg;
	erg = var1^var2;
	return (var1^var2);
}

int bitor_funktion(int var1, int var2){
	return (var1|var2);
}

int bitand_funktion(int var1, int var2){
	return (var1 & var2);
}

int lognot_funktion(int var1, int var2){
	return (!(var1<var2));
}

int logand_funktion(int var1, int var2){
	return (var1<2 && 4<var2);
}

int logor_funktion(int var1, int var2){
	return (var1<2 || 4<var2);
}

int test_funktion(){
	int i;
	//mem[0] = zeiger_funktion(3);
	//mem[1] = umwandlung_funktion();
	//mem[3] = dereferenzierung_funktion(12, 144);
	for (i=0; i<33; i++){
	mem[i] = shift_funktion1(0xFFFFFFFF, i);
	//mem[5] = shift_funktion2(0xFFFFFFFF, i);
	
	}
	mem[33] = shift_funktion3(0xFFFFFFFF, 32);
	mem[34] = 5;
	//mem[7] = bitnot_funktion(45);
	//mem[8] = bitxor_funktion(45,35);
	//mem[9] = bitand_funktion(45,35);
	//mem[10]= bitor_funktion(45,35);
	//mem[11]= lognot_funktion(2,3);
	//mem[12]= logand_funktion(1,5);
	//mem[13]= logor_funktion(2,4);
}

