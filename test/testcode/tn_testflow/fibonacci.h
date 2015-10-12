//die maximale kommentarlänge in den dateien betraegt 1024byte

//anzahl der ints mit denen der allokierte speicher befuellt werden soll
#define size 10
int mem[size];

int fibonacci(int z){
	return (z<=1)? 1:fibonacci(z-1) + fibonacci(z-2);
}

void test_funktion(){
	int i;
	for(i=0; i<=size; i++){
		mem[i] = fibonacci(i);
		//printf("%d, %d \n", i, fibonacci(i));
	}
}
