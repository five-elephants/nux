//die maximale kommentarlänge in den dateien betraegt 1024byte

//anzahl der ints mit denen der allokierte speicher befuellt werden soll
int size = 101;
int mem[101];

int fibonacci(int z){
	return (z<=1)? 1:fibonacci(z-1) + fibonacci(z-2);
}


void test_funktion(){
	int i;

	for(i=0; i<51; i++){
/*		if(i==10) {mem[i]=fibonacci(i/5);}
		else if(i==20) {mem[i]=fibonacci(i/5);}	
		else if(i==30) {mem[i]=fibonacci(i/5);}
		else if(i==40) {mem[i]=fibonacci(i/5);}
		else if(i==50) {mem[i]=fibonacci(i/5);}
		else {mem[i] = 1;}
*/	

		switch(i){
			case 10: mem[i]=fibonacci(i/5);
				break;
		
			case 20: mem[i]=fibonacci(i/5);
				break;
		
			case 30: mem[i]=fibonacci(i/5);
				break;
		
			case 40: mem[i]=fibonacci(i/5);
				break;
		
			case 50: mem[i]=fibonacci(i/5);
				break;
 
			default: mem[i]=1;
		}

	}

	for(i=50; i<101; i++){
		switch(i){
			case 10: mem[i]=10;
				break;
		
			case 20: mem[i]=20;
				break;
		
			case 30: mem[i]=30;
				break;
		
			case 40: mem[i]=40;
				break;
		
			case 50: mem[i]=50;
				break;
 
			default: mem[i]=1;
		}
	}

}


