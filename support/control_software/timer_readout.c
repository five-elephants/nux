#include <stdio.h>
#include <stdlib.h>


int timer_ad(){
        FILE *pFile;
        int a;
        pFile = fopen ("temp_timer_ad.txt","r");
        fscanf(pFile, "%x", &a);
        fclose(pFile);
        return (a-0x40000000);
}


int main(){
	FILE *pFile, *pFile2;
	int i = 0;
	int j = 0;
	int counter = 0;
	char *c = malloc(1024);
	int a[8], time_arr[8];
	unsigned int b, rv[2], z;
	unsigned int start_ad, time_hex;
	char *time_byte = malloc(1024);	
	start_ad = timer_ad();
//	printf("%d \n \n", start_ad);
	pFile = fopen("result_byte.txt","r");

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
//                              printf("%d ", a);
                                if(c[0] == 'x' && c[1] == 'x') {fprintf(pFile2, "00 ");}
                                else {fprintf(pFile2, "%s ", c);}
                                if(i%4 == 0) fprintf(pFile2, "\n");
//                              if(i%4 == 0) printf("\n");
                        }
                }

                fclose (pFile);
                fclose (pFile2);

        }

	
	pFile = fopen("temp_dump.mem","r");
	printf("measured time in us: ");

	while(j < (start_ad + 8)){
		j++;
		fscanf(pFile, "%x", &time_hex);
		//printf("%x, %d ", time_hex, j);
		if(j > start_ad){
	//		printf("//%d, %x \n", j, time_hex);
			time_arr[counter] = time_hex;
			counter++;
		}
	}
	
	fclose(pFile);
		
	rv[0] = (time_arr[0] << 24) |  (time_arr[1] << 16) | (time_arr[2] << 8) | time_arr[3];  
	rv[1] = (time_arr[4] << 24) |  (time_arr[5] << 16) | (time_arr[6] << 8) | time_arr[7];  



/*	b = 0;
	rv[0] = time_arr[0] | b;
	rv[1] = time_arr[4] | b;





	for(i=1; i<4; i++){
		b = rv[0];	
		rv[0] = (b << 8) | time_arr[i];
//		printf("%d, %d \n", i, rv[0]);
	}
	
	b = 0;

	for(i=5; i<8; i++){
		b = rv[1];
		rv[1] = (b << 8) | time_arr[i];
//		printf("%d, %d \n", i, rv[1]);

	}
*/	
	if(rv[0] > 0){ 
		printf("%d %d\n", rv[0], rv[1]);
	}
	
	else{
		printf("%d\n", rv[1]);
	}

	free(time_byte);

return 0;
}
