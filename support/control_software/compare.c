#include <stdio.h>
#include <stdlib.h>

//die maximale kommentarlänge in den dateien betraegt 1024byte



int cmp_ad(){
	FILE *pFcomp;
	int a, b;
	pFcomp = fopen ("temp_mem_ad.txt","r");
	fscanf(pFcomp, "%x", &a);
	fclose(pFcomp);
	pFcomp = fopen ("emp_mem_ad.txt","w");
	fprintf(pFcomp, "%d", (a-0x40000000));
	fclose(pFcomp);
	pFcomp = fopen("emp_mem_ad.txt", "r");
	fscanf(pFcomp,"%d", &b);
	fclose(pFcomp);
	return b;
}


void compare(int cmpad, int size){
	
	int i, indikator;
	char *dump = malloc(1024 + 4*size);
	char *endian = malloc(1024); 
	

	FILE *pFiledump;
	FILE *pFileendian;
	
	pFiledump = fopen ("result_byte.txt","r");
	pFileendian = fopen ("referenzsystem.txt","r");
	
	i = 0;		
		while(i < cmpad){
		i++;
			
		fscanf (pFiledump, "%s", dump);
		
		//ausblendung der kommentare
		if((dump[0] == '/') && (dump[1] == '/')) {
			while(fgetc(pFiledump) != '\n');
			i--;
		} 
		
		else {
			printf("%d, %s \n",i, dump);		
		}
	}
	
	indikator = 1;
	printf("index, s2pp-fpga, referenzsystem\n");
	for(i = 0; i < (4*size); i++){
		fscanf(pFiledump, "%s", dump);
		fscanf(pFileendian, "%s", endian);
		
		if(strcmp(dump, endian) != 0){
			printf("%d mismatch in ", i);
			indikator = 0;
		}
		
		printf("%d, %s, %s \n", i, dump, endian);
	}
	
	fclose (pFiledump);
	fclose (pFileendian);

	free(endian);
	free(dump);
	
	if(indikator == 1) printf("match \n");
}
 

int main(int argc, char *argv[]){
	//Initialisierung allokierter Bereich wird mit 0 initialisiert
	int cmpad, size;
	if(!argv[1]){
	printf("no compare size given! \n", size);
	}
	
	else{
		size = atoi(argv[1]);

		cmpad = cmp_ad();
		compare(cmpad, size);
	}
return 0;
}	

