#include<iostream>
#include<string.h>
#include<stack>
using namespace std;
int lp=0;
int i,k;
int retnum=0;
int vnum=0;
int rnu=0;
int stanum=0;
char* substring(char a[],int s,int e){
	char *r= (char*)malloc(sizeof(char)*100);
	int i,k=0;
	for(i=s;i<=e;i++){
		r[k]=a[i];
		k++;
	}
	r[k]='\0';
	return r;
} 
int calval(char *a){
	int sum=0,q=1;
	for(int i=strlen(a)-1;i>=0;i--){

		int wer;
		wer=a[i];
		int y=wer-48;
		sum=sum+q*y;
		q=q*10;			
	}
	return sum;
}
int ind=0;
int infun=0;
main(int argc,char* argv[4]){
	FILE *p1,*p2,*p3;
	int c=0;
	int pl=0,vs=1;
	//opening files
	p1=fopen(argv[1],"r");
	p2=fopen(argv[2],"w");
	char b[100];
	char p[100];
	//using fgets on asm file into buffer b till feof
	while(fgets(b,100,p1)){
		int w=0;
		while(b[w]==' '||b[w]=='\t') w++;
		//checking each character in b for unwanted values like comments, space, etc..
		for(i=w,k=0;i<100;i++){
			if(b[i]=='\n'||b[i]=='\r') break;
			if(i!=0&&(b[i-1]=='\t'||b[i-1]==' ')&&(b[i]=='\t'||b[i]==' ')) continue;
			if(b[i]=='/'&&b[i+1]=='/') break;
			//in multi line comment when /* is encountered make c=1.
			if(b[i]=='/'&&b[i+1]=='*'){
				 c=1;
				 i=i+2;
			}
			//if c=1 ignore all chars till */ appears. then make c=0.
			if(c==1){
				while(i<=99){
					if(b[i]=='*'&&b[i+1]=='/'){
						c=0;
						i=i+2;
						break;
					}
					i++;
				}
				if(i==100) break;
			}
			//again check for unwanted values in case comment has just ended 
			if(b[i]=='\n'||b[i]=='\r') break;
			if(b[i]=='/'&&b[i+1]=='/') break;
			if(i!=0&&(b[i-1]=='\t'||b[i-1]==' ')&&(b[i]=='\t'||b[i]==' ')) continue;
			//input the required charecters into another array
			p[k]=b[i];
			k++;
		}
		p[k]='\0';
		if(!*p) continue;
		fputs(p,p2);
		fputc('\n',p2);
		lp++;
	}
	fclose(p1);
	fclose(p2);
	int local[100],arg[100];
	//opening ir and hack files
	stack<int> s;
	p2=fopen(argv[2],"r");
	p3=fopen(argv[3],"w");
	char buff[100],alu[100],buff1[100];
	while(fgets(buff,100,p2)){
		char *funnam;
		funnam=buff;
		int v1=0;
		while((buff[v1]!='\n'&&buff[v1]!=' '&&buff[v1]!='\t'&&buff[v1]!='\r')&&v1<strlen(buff)){
			buff1[v1]=buff[v1];
			funnam++;
			v1++;
		}
		buff1[v1]='\0';
		funnam++;
		if(strstr(buff1,"function")){
			char funnam1[100];
			int u=0;
			while(funnam[u]!='\0'&&funnam[u]!=' '){
				funnam1[u]=funnam[u];
				u++;
			}
			funnam1[u]='\0';
			fputc('(',p3);
			fputs(funnam1,p3);
			fputs(")\n",p3);
			fprintf(p3,"@%sD=A\n",funnam+u+1);
			fprintf(p3,"(vloop%s%d)\n",argv[1],vnum);
			fprintf(p3,"@vend%s%d\nD;JEQ\n",argv[1],vnum);
			fputs("@SP\nM=M+1\nA=M-1\nM=0\n",p3);
			fprintf(p3,"D=D-1\n");
			fprintf(p3,"@vloop%s%d\n0;JMP\n",argv[1],vnum);
			fprintf(p3,"(vend%s%d)\n",argv[1],vnum);
			vnum++;
			continue;
		}
		if(strstr(buff1,"call")){
			char funnam1[100];
			int u=0;
			while(funnam[u]!='\0'&&funnam[u]!=' '){
				funnam1[u]=funnam[u];
				u++;
			}
			funnam1[u]='\0';
			fprintf(p3,"@retadd%s%d\n",argv[1],retnum);
			fputs("D=A\n@SP\nM=M+1\nA=M-1\nM=D\n",p3);
			fputs("@LCL\nD=M\n@SP\nM=M+1\nA=M-1\nM=D\n",p3);
			fputs("@ARG\nD=M\n@SP\nM=M+1\nA=M-1\nM=D\n",p3);
			fputs("@THIS\nD=M\n@SP\nM=M+1\nA=M-1\nM=D\n",p3);
			fputs("@THAT\nD=M\n@SP\nM=M+1\nA=M-1\nM=D\n",p3);
			fprintf(p3,"@SP\nD=M\n@%sD=D-A\n@5\nD=D-A\n@ARG\nM=D\n",funnam+u+1);
			fputs("@SP\nD=M\n@LCL\nM=D\n",p3);
			fputc('@',p3);
			fputs(funnam1,p3);
			fputc('\n',p3);
			fputs("0;JMP\n",p3);
			fprintf(p3,"(retadd%s%d)\n",argv[1],retnum);
			retnum++;		
			continue;		
		}
		if(strstr(buff1,"return")){
			fputs("@LCL\nD=M\n",p3);
			fprintf(p3,"@frame%s%d\nM=D\n",argv[1],rnu);
			fprintf(p3,"@frame%s%d\nD=M\n@5\nA=D-A\nD=M\n@ret%s%d\nM=D\n",argv[1],rnu,argv[1],rnu);
			fputs("@SP\nAM=M-1\nD=M\n@ARG\nA=M\nM=D\n",p3);
			fputs("@ARG\nD=M+1\n@SP\nM=D\n",p3);
			fprintf(p3,"@frame%s%d\nA=M-1\nD=M\n@THAT\nM=D\n",argv[1],rnu);
			fprintf(p3,"@frame%s%d\nD=M\n@2\nA=D-A\nD=M\n@THIS\nM=D\n",argv[1],rnu);
			fprintf(p3,"@frame%s%d\nD=M\n@3\nA=D-A\nD=M\n@ARG\nM=D\n",argv[1],rnu);
			fprintf(p3,"@frame%s%d\nD=M\n@4\nA=D-A\nD=M\n@LCL\nM=D\n",argv[1],rnu);
			fprintf(p3,"@ret%s%d\nA=M\n0;JMP\n",argv[1],rnu);
			rnu++;
			continue;
		}
		if(strstr(buff,"label")){
			fputc('(',p3);
			if(buff[strlen(buff)-2]==' ')
				fputs(substring(buff,6,strlen(buff)-3),p3);
			else
				fputs(substring(buff,6,strlen(buff)-2),p3);
			fputc(')',p3);
			fputc('\n',p3);
			continue;
		}
		if(strstr(buff,"add")){
			FILE *temp;
			char temp1[100];
			temp=fopen("add.txt","r");
			while(fgets(temp1,100,temp)) fputs(temp1,p3);
			continue;
		}
		if(strstr(buff,"sub")){
			FILE *temp;
			char temp1[100];
			temp=fopen("sub.txt","r");
			while(fgets(temp1,100,temp)) fputs(temp1,p3);
			continue;
		}
		if(strstr(buff,"and")){
			FILE *temp;
			char temp1[100];
			temp=fopen("and.txt","r");
			while(fgets(temp1,100,temp)) fputs(temp1,p3);
			continue;
		}
		if(strstr(buff,"or")){
			FILE *temp;
			char temp1[100];
			temp=fopen("or.txt","r");
			while(fgets(temp1,100,temp)) fputs(temp1,p3);
			continue;
		}
		if(strstr(buff,"not")){
			FILE *temp;
			char temp1[100];
			temp=fopen("not.txt","r");
			while(fgets(temp1,100,temp)) fputs(temp1,p3);
			continue;
		}
		if(strstr(buff,"neg")){
			FILE *temp;
			char temp1[100];
			temp=fopen("neg.txt","r");
			while(fgets(temp1,100,temp)) fputs(temp1,p3);
			continue;
		}
		if(strstr(buff,"gt")){
			FILE *temp;
			char temp1[100];
			temp=fopen("gt.txt","r");
			while(fgets(temp1,100,temp)){
				cout<<strcmp(temp1,"(end)\n")<<" "<<temp1<<" ";
				if(strcmp(temp1,"(end)\n")-3==0){
					fprintf(p3,"(end%d)\n",ind);
					continue;
				}
				if(strcmp(temp1,"@end\n")-3==0){
					fprintf(p3,"@end%d\n",ind);
					continue;
				}
				fputs(temp1,p3);
			}
			ind++; 
			continue;
		}
		if(strstr(buff,"lt")){
			FILE *temp;
			char temp1[100];
			temp=fopen("lt.txt","r");
			while(fgets(temp1,100,temp)){
				if(strcmp(temp1,"(end)\n")-3==0){
					fprintf(p3,"(end%d)\n",ind);
					continue;
				}
				if(strcmp(temp1,"@end\n")-3==0){
					fprintf(p3,"@end%d\n",ind);
					continue;
				}
				 fputs(temp1,p3);
			}
			ind++;
			continue;
		}
		if(strstr(buff,"eq")){
			FILE *temp;
			char temp1[100];
			temp=fopen("eq.txt","r");
			while(fgets(temp1,100,temp)){
				if(strcmp(temp1,"(end)\n")-3==0){
					fprintf(p3,"(end%d)\n",ind);
					cout<<ind;
					continue;
				}
				if(strcmp(temp1,"@end\n")-3==0){
					fprintf(p3,"@end%d\n",ind);
					cout<<ind;
					continue;
				}
				fputs(temp1,p3);
			} 
			ind++;
			continue;
		}
		if(strstr(buff,"goto")){
			if(!strstr(buff,"if")){
				fputc('@',p3);
				fputs(substring(buff,5,strlen(buff)-2),p3);
				fputc('\n',p3);
				fputs("0;JMP\n\0",p3);
				continue;
			}
			else{
				fputs("@SP\nA=M-1\nD=M\n",p3);
				fputs("@SP\nAM=M-1\nM=0\n",p3);
				fputc('@',p3);
				fputs(substring(buff,8,strlen(buff)-2),p3);
				fputc('\n',p3);
				fputs("D;JNE\n\0",p3);
				continue;
			}

		}
		if(strstr(buff1,"push")){
			fputc('@',p3);
			if(strstr(buff,"constant")){
				fputs(substring(buff,14,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
			}
			if(strstr(buff,"argument")){
				fputs(substring(buff,14,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
				fputc('@',p3);
				fputs("ARG\n",p3);
				fputs("A=M+D\n",p3);
				fputs("D=M\n",p3);
			}
			if(strstr(buff,"local")){
				fputs(substring(buff,11,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
				fputc('@',p3);
				fputs("LCL\n",p3);
				fputs("A=M+D\n",p3);
				fputs("D=M\n",p3);
			}
			if(strstr(buff,"this")){
				fputs(substring(buff,10,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
				fputc('@',p3);
				fputs("THIS\n",p3);
				fputs("A=M+D\n",p3);
				fputs("D=M\n",p3);
			}
			if(strstr(buff,"that")){
				fputs(substring(buff,10,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
				fputc('@',p3);
				fputs("THAT\n",p3);
				fputs("A=M+D\n",p3);
				fputs("D=M\n",p3);
			}
			if(strstr(buff,"pointer")){
				if(strstr(buff,"0")){
					fputs("THIS\n",p3);
					fputs("D=M\n",p3);
				}
				if(strstr(buff,"1")){
					fputs("THAT\n",p3);
					fputs("D=M\n",p3);
				}
			}
			if(strstr(buff,"temp")){
				 int w=calval(substring(buff,10,strlen(buff)-2));  
				fprintf(p3,"R%d\n",w+5);
				fputs("D=M\n",p3);                                                                                      
			}
			if(strstr(buff,"static")){
				fprintf(p3,"stat%s",argv[1],stanum);
				fputs(substring(buff,12,strlen(buff)-1),p3);
				fputs("D=M\n",p3);
				
			}

			FILE *temp;
			char temp1[100];
			temp=fopen("push.txt","r");
			while(fgets(temp1,100,temp)) fputs(temp1,p3);
		}
		if(strstr(buff,"pop")){
			FILE *temp;
			char temp1[100];
			temp=fopen("pop.txt","r");
			
			if(strstr(buff,"argument")){
				fputc('@',p3);
				fputs(substring(buff,13,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
				fputs("@ARG\n",p3);
				fputs("D=D+M\n",p3);
			}
			if(strstr(buff,"local")){
				fputc('@',p3);
				fputs(substring(buff,10,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
				fputs("@LCL\n",p3);
				fputs("D=D+M\n",p3);
				//continue;
			}
			if(strstr(buff,"this")){
				fputc('@',p3);
				fputs(substring(buff,9,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
				fputs("@THIS\n",p3);
				fputs("D=D+M\n",p3);
				//continue;
			}
			if(strstr(buff,"that")){
				fputc('@',p3);
				fputs(substring(buff,9,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
				fputs("@THAT\n",p3);
				fputs("D=D+M\n",p3);
				//continue;
			}
			if(strstr(buff,"pointer")){
				if(strstr(buff,"0")){
					fputs("@THIS\n",p3);
					fputs("D=A\n",p3);
				}
				if(strstr(buff,"1")){
					fputs("@THAT\n",p3);
					fputs("D=A\n",p3);
				}
			}
			if(strstr(buff,"temp")){
				 int w=calval(substring(buff,9,strlen(buff)-2));
				fprintf(p3,"@R%d\n",w+5);
				fputs("D=A\n",p3);
				                                                                                                            
			}
			if(strstr(buff,"static")){
				fputc('@',p3);
				fprintf(p3,"stat%s",argv[1]);
				fputs(substring(buff,11,strlen(buff)-1),p3);
				fputs("D=A\n",p3);
			}
			while(fgets(temp1,100,temp)) fputs(temp1,p3);

		}
	}
}