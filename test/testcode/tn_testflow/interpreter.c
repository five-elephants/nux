// Copyright 2015 Heidelberg University Copyright and related rights are
// licensed under the Solderpad Hardware License, Version 0.51 (the "License");
// you may not use this file except in compliance with the License. You may obtain
// a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
// required by applicable law or agreed to in writing, software, hardware and
// materials distributed under this License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
// the License for the specific language governing permissions and limitations
// under the License.


#include<stdio.h>
#include<stdlib.h>

int main (){
	FILE *pFile, *pFile2, *pFile3;
	char *c = malloc(1024);
	unsigned int a;
	char *str = "x";
	int i = 0;
	pFile=fopen ("/afs/kip.uni-heidelberg.de/user/tnonne/s2pp-source/dump_c_coremark.mem","r");
	

	//erstellung einer Datei, die dasselbe dump-format wie der fpga-dump hat
	pFile2 = fopen("temp_dump.mem","w");
	if(pFile == NULL) perror ("Error opening file");
	else {
		while (!feof(pFile)){
			i++;
			fscanf(pFile, "%s", c);
						
			if((c[0] == '/') && (c[1] == '/')) {
                        	while(fgetc(pFile) != '\n');
                        	i--;
	                }
			
			if(i > 0){
//				printf("%d ", a);
				if(c[0] == 'x' && c[1] == 'x') {fprintf(pFile2, "00 ");}
				else {fprintf(pFile2, "%s ", c);}
				if(i%4 == 0) fprintf(pFile2, "\n");
//				if(i%4 == 0) printf("\n");
			}
		}

		fclose (pFile);
		fclose (pFile2);

	}

	//ascii-interpretation der datei
	pFile3 = fopen("temp_dump.mem","r");

	if(pFile3 == NULL) perror ("Error opening file");
	else {
		printf("Adresse: ascii-Interpretation \n");
		i = 0;
		while (!feof(pFile3)){
			if(i%4 == 0) printf("%d :", i);
			fscanf(pFile3, "%x", &a);
			printf("%c", a);
			i++;
			if(i%4 == 0) printf("\n");
		}

                printf("\n");
                fclose (pFile3);

	}


return 0;
}	

