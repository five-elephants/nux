//int size = 35;
int size = 258;
int mem[258];

int shift_funktion3(int var, int shift){
	int erg;
	erg = (var << shift);
	return erg;
}

int shift_funktion1(int var, int shift){
	return (var << shift);
}

//Stimmt nicht überein; Unterschiedliche Definitionen für Schiebeoperator?
int test_funktion(){
	int i;
	int a = 0x00FFFFFF;
	for(i=0; i<258; i++){
		mem[i] = shift_funktion3(a+i, 32);
		//mem[i] = (a+i)/4294967296; //das ist 2^32
	}
	
/*
//hier ist das resultat irgendwie inkonsistent!!	
	for (i=0; i<33; i++){
		mem[i] = shift_funktion3(0xFFFFFFFF, i);
	}
	mem[33] = shift_funktion3(0xFFFFFFFF, 32);
	//markierung des endes
	mem[34] = 5;
*/


}
