#include<stdio.h>
#include<stdlib.h>

int main (){
	FILE * pFile;
	unsigned int c;
	int i = 0;
	pFile=fopen ("result_byte.txt","r");
	if(pFile==NULL) perror ("Error opening file");
	else {
		printf("Adresse: ascii-Interpretation \n");	
		while (!feof(pFile)){
			if(i%4 == 0) printf("%d :", i);
			fscanf(pFile, "%x", &c);
			printf("%c", c);	
			i++;
			if(i%4 == 0) printf("\n");

		}
		printf("\n");
		fclose (pFile);
	}
return 0;
}	

