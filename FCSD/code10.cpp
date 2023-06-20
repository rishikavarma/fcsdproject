#include<iostream>
#include<string.h>
#include<stack>
#include<vector>
using namespace std;
int subr=0,lablenum;
struct node{
	char name[100];
	char kind[100];
	char type[100];
	int index;
};
struct srtab{
	char fun[100];
	char funtype[100];
	vector<node> sv;
	int ac=0;
	int lc=0;
};

struct classtab{
	vector<node> cv;
	int fc=0;
	int sc=0;
};
int labelname;
vector<classtab> tabv;
classtab xy;
vector<srtab> vs;
int lp=0,non;
char curclass[10000];
vector<char*> fname;
char* substring(char a[],int s,int e){
	char *r= (char*)malloc(sizeof(char)*100);
	int i,kl=0;
	for(i=s;i<=e;i++){
		r[kl]=a[i];
		kl++;
	}
	r[kl]='\0';
	return r;
} 
bool checkint(char a[]){
	for(int i=0;i<strlen(a);i++)
		if(a[i]!='0'&&a[i]!='1'&&a[i]!='2'&&a[i]!='3'&&a[i]!='4'&&a[i]!='5'&&a[i]!='6'&&a[i]!='7'&&a[i]!='8'&&a[i]!='9') return false;
	return true;
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
char* recognise(char a[]){
	char* h;
	if(!strcmp(a,"class")||!strcmp(a,"constructor")||!strcmp(a,"function")||!strcmp(a,"method")||!strcmp(a,"field")||!strcmp(a,"static")||!strcmp(a,"var")||!strcmp(a,"int")||!strcmp(a,"char")||!strcmp(a,"boolean")||!strcmp(a,"void")||!strcmp(a,"true")||!strcmp(a,"false")||!strcmp(a,"null")||!strcmp(a,"this")||!strcmp(a,"let")||!strcmp(a,"do")||!strcmp(a,"if")||!strcmp(a,"else")||!strcmp(a,"while")||!strcmp(a,"return")){
		return "keyword\0";
	}
	else if(!strcmp(a,"{")||!strcmp(a,"}")||!strcmp(a,"(")||!strcmp(a,")")||!strcmp(a,"[")||!strcmp(a,"]")||!strcmp(a,".")||!strcmp(a,",")||!strcmp(a,";")||!strcmp(a,"+")||!strcmp(a,"-")||!strcmp(a,"*")||!strcmp(a,"/")||!strcmp(a,"&")||!strcmp(a,"|")||!strcmp(a,"<")||!strcmp(a,">")||!strcmp(a,"=")||!strcmp(a,"~")){
		return "symbol\0";
	}
	else if(checkint(a)){
		return "integerconstant\0";
	}
	else if(a[0]=='"'||a[strlen(a)-1]=='"'){
		return "stringconstant\0";
	}
	else return "identifier\0";
}
FILE *k1,*k2;
FILE* err;
char del[10000],del1[10000];
int flag=0,flag1=0;
int k=0;
char prob[10000];
char* tokbok(char buff[]);
bool varuse(char a[]);
bool elsest();
bool exp();
bool exp(char c[]);
bool returnst();
bool term(char a[]);
bool dost();
bool ifst();
bool whilest();
bool letst();
bool explist();
bool keysym(char*a,char* ks,char* na);
bool subrcall(){
	char a[10000];
	fgets(a,10000,k1);
	if(strstr(a,"<identifier>")){
		fputs(a,k2);
		fgets(a,10000,k1);
		if(strstr(a,"<symbol>(")){
			fputs(a,k2);
			if(!explist())return false;
			return true;
		}
		else if(strstr(a,"<symbol>.")){
			fputs(a,k2);
			fgets(a,10000,k1);
			if(strstr(a,"<identifier>")){
				fputs(a,k2);
				fgets(a,10000,k1);
				if(strstr(a,"<symbol>(")){
					fputs(a,k2);
					if(!explist())return false;
					return true;
				}
			}
		}
	}
	return false;
}
bool explist(){
	char a[10000];
	fputs("<expressionlist>\n",k2);
	fgets(a,10000,k1);
	while(!strstr(a,"<symbol>)")){
		if(!exp(a))return false;
		strcpy(a,del1);
		if(strstr(a,"<symbol>)"))break;
		if(!keysym(a,"symbol",",")) return false;
		fgets(a,10000,k1);
	}
	fputs("</expressionlist>\n",k2);
	fputs(a,k2);
	return true;
}
bool term(char a[]){
	fputs("<term>\n",k2);
	if(strstr(a,"<symbol>-")||strstr(a,"<symbol>~")){
		fputs(a,k2);
		fgets(a,10000,k1);
		if(!term(a))return false;
		fputs("</term>\n",k2);
		return true;
	}
	
	if(strstr(a,"<integerconstant>")||strstr(a,"<stringconstant>")||strstr(a,"<keyword>true</keyword>")||strstr(a,"<keyword>false</keyword>")||strstr(a,"<keyword>this</keyword>")||strstr(a,"<keyword>null</keyword>")){
		fputs(a,k2);
		fputs("</term>\n",k2);
		return true;
	}
	if(strstr(a,"<identifier>")){
		char daf[10000];
		strcpy(daf,a);
		//
		fputs(a,k2);
		fgets(a,10000,k1);
		if(!strstr(a,"<symbol>(")&&!strstr(a,"<symbol>[")&&!strstr(a,"<symbol>.")){
			if(!varuse(daf))return false;
			strcpy(del,a);
			flag=1;
			fputs("</term>\n",k2);
			return true;
		}
		else if(strstr(a,"<symbol>[")){
			if(!varuse(daf))return false;
			fputs(a,k2);
			if(!exp()) return false;
			strcpy(a,del1);
			if(!keysym(a,"symbol","]"))return false;
			fputs("</term>\n",k2);
			return true;
		}
		else if(strstr(a,"<symbol>.")){
			fputs(a,k2);
			fgets(a,10000,k1);
			fputs(a,k2);
			fgets(a,10000,k1);
			if(strstr(a,"<symbol>(")){
				fputs(a,k2);
				if(!explist())return false;
			}
			fputs("</term>\n",k2);
			return true;
		}
		else if(strstr(a,"<symbol>(")){
			fputs(a,k2);
			if(!explist())return false;
			fputs("</term>\n",k2);
			return true;
		}
		return true;
	}
	else if(strstr(a,"<symbol>(")){
		fputs(a,k2);
		if(!exp())return false;
		strcpy(a,del1);
		if(!keysym(a,"symbol",")"))return false;
		fputs("</term>\n",k2);
		return true;
	}
	fprintf(err,"Expecting term but %s",tokbok(a));
	return false;
}
bool exp(){
	char c[10000];
	fputs("<expression>\n",k2);
	fgets(c,10000,k1);
	
	if(!term(c))return false;
	if(flag==1){
		strcpy(c,del);
		flag=0;
	}
	else fgets(c,10000,k1);
	while(strstr(c,"<symbol>+</symbol>\n")||strstr(c,"<symbol>-</symbol>\n")||strstr(c,"<symbol>*</symbol>\n")||strstr(c,"<symbol>/</symbol>\n")||strstr(c,"<symbol>&</symbol>\n")||strstr(c,"<symbol>|</symbol>\n")||strstr(c,"<symbol><</symbol>\n")||strstr(c,"<symbol>></symbol>\n")||strstr(c,"<symbol>=</symbol>\n")){
		fputs(c,k2);
		fgets(c,10000,k1);
		if(!term(c))return false;
		if(flag==1){
			strcpy(c,del);
			flag=0;
		}
		else fgets(c,10000,k1);
	}
	fputs("</expression>\n",k2);
	strcpy(del1,c);
	return true;
}
bool exp(char c[10000]){
	fputs("<expression>\n",k2);	
	if(!term(c))return false;
	if(flag==1){
		strcpy(c,del);
		flag=0;
	}
	else fgets(c,10000,k1);
	while(strstr(c,"<symbol>+</symbol>\n")||strstr(c,"<symbol>-</symbol>\n")||strstr(c,"<symbol>*</symbol>\n")||strstr(c,"<symbol>/</symbol>\n")||strstr(c,"<symbol>&</symbol>\n")||strstr(c,"<symbol>|</symbol>\n")||strstr(c,"<symbol><</symbol>\n")||strstr(c,"<symbol>></symbol>\n")||strstr(c,"<symbol>=</symbol>\n")){
		fputs(c,k2);
		fgets(c,10000,k1);
		if(!term(c))return false;
		if(flag==1){
			strcpy(c,del);
			flag=0;
		}
		else fgets(c,10000,k1);
	}
	fputs("</expression>\n",k2);
	strcpy(del1,c);
	return true;
}
bool varuse(char a[]){
	if(!strstr(a,"<identifier>")){
		fputs("Expected type Identifier",err);
		return false;
	}
		int i=vs.size()-1;
		for(int j=0;j<vs[i].sv.size();j++){
			if(strstr(a,vs[i].sv[j].name))return true;
		}
	
	for(int i=0;i<xy.cv.size();i++){
		if(strstr(a,xy.cv[i].name)) return true;
	}
	for(int i=0;i<fname.size();i++){
		if(strstr(a,fname[i]))return true;
	}
	fprintf(err,"Declaration error: %s undeclared.",tokbok(a));
	return false;
}
bool letst(){
	char a[10000];
	fgets(a,10000,k1);
	if(!varuse(a))  return false;
	fputs(a,k2);
	fgets(a,10000,k1);
	if(strstr(a,"<symbol>[</symbol>")){
		fputs(a,k2);
		if(!exp()) return false;
		strcpy(a,del1);
		if(!keysym(a,"symbol\0","]\0"))return false;
		fgets(a,10000,k1);
	}
	if(!keysym(a,"symbol\0","=\0"))return false;
	if(!exp()) return false;
	strcpy(a,del1);
	if(!keysym(a,"symbol\0",";\0"))return false;
	return true;
}
bool ifst(){
	char c[10000];
	fgets(c,10000,k1);
	if(!keysym(c,"symbol\0","(\0"))return false;
	if(!exp()) return false;
	strcpy(c,del1);
	if(!keysym(c,"symbol\0",")\0"))return false;
	fgets(c,10000,k1);
	if(!keysym(c,"symbol\0","{\0"))return false;
	fgets(c,10000,k1);
	if(strstr(c,"<keyword>let</keyword>\n")||strstr(c,"<keyword>while</keyword>\n")||strstr(c,"<keyword>if</keyword>\n")||strstr(c,"<keyword>do</keyword>\n")||strstr(c,"<keyword>return</keyword>\n")){
		fputs("<statements>\n",k2);
		k++;
		while(strstr(c,"<keyword>let</keyword>\n")||strstr(c,"<keyword>while</keyword>\n")||strstr(c,"<keyword>if</keyword>\n")||strstr(c,"<keyword>do</keyword>\n")||strstr(c,"<keyword>return</keyword>\n")){
			if(strstr(c,"<keyword>let</keyword>\n")){
				fputs("<letstatement>\n",k2);
				k++;
				fputs(c,k2);
				if(!letst())return false;
				fputs("</letstatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>while</keyword>\n")){
				fputs("<whilestatement>\n",k2);
				k++;
				fputs(c,k2);
				if(!whilest())return false;
				k--;
				fputs("</whilestatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>if</keyword>\n")){
				fputs("<ifstatement>\n",k2);
				k++;
				fputs(c,k2);
				if(!ifst())return false;
				fgets(c,10000,k1);
				if(strstr("<keyword>else</keyword>\n",c)){
					fputs(c,k2);
					if(!elsest())return false;
					fgets(c,10000,k1);
				}
				k--;
				fputs("</ifstatement>\n",k2);
			}
			else if(strstr(c,"<keyword>do</keyword>\n")){
				fputs("<dostatement>\n",k2);
				k++;
				fputs(c,k2);
				if(!dost())return false;
				k--;
				fputs("</dostatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>return</keyword>\n")){
				fputs("<returnstatement>\n",k2);
				fputs(c,k2);
				if(!returnst())return false;
				fputs("</returnstatement>\n",k2);
				fgets(c,10000,k1);
			}
		}
		fputs("</statements>\n",k2);
	}
	if(!keysym(c,"symbol\0","}\0"))return false;
	return true;
}
bool elsest(){
	//return true;
	char c[10000];
	fgets(c,10000,k1);
	if(!keysym(c,"symbol\0","{\0"))return false;
	fgets(c,10000,k1);
	if(strstr(c,"<keyword>let</keyword>\n")||strstr(c,"<keyword>while</keyword>\n")||strstr(c,"<keyword>if</keyword>\n")||strstr(c,"<keyword>do</keyword>\n")||strstr(c,"<keyword>return</keyword>\n")){
		
		fputs("<statements>\n",k2);
		while(strstr(c,"<keyword>let</keyword>\n")||strstr(c,"<keyword>while</keyword>\n")||strstr(c,"<keyword>if</keyword>\n")||strstr(c,"<keyword>do</keyword>\n")||strstr(c,"<keyword>return</keyword>\n")){
			if(strstr(c,"<keyword>let</keyword>\n")){
				
				fputs("<letstatement>\n",k2);
				
				fputs(c,k2);
				if(!letst())return false;
			
				fputs("</letstatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>while</keyword>\n")){
				
				fputs("<whilestatement>\n",k2);
				
				fputs(c,k2);
				if(!whilest())return false;
				fputs("</whilestatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>if</keyword>\n")){
				fputs("<ifstatement>\n",k2);
				fputs(c,k2);
				if(!ifst())return false;
				fgets(c,10000,k1);
				if(strstr("<keyword>else</keyword>\n",c)){
					fputs(c,k2);
					if(!elsest())return false;
					fgets(c,10000,k1);
				}
				fputs("</ifstatement>\n",k2);
			}
			else if(strstr(c,"<keyword>do</keyword>\n")){
				fputs("<dostatement>\n",k2);
				fputs(c,k2);
				if(!dost())return false;
				k--;
				fputs("</dostatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>return</keyword>\n")){
				fputs("<returnstatement>\n",k2);
				k++;
				fputs(c,k2);
				if(!returnst())return false;
				k--;
				fputs("</returnstatement>\n",k2);
				fgets(c,10000,k1);
			}
		}
		fputs("</statements>\n",k2);
	}
	if(!keysym(c,"symbol\0","}\0"))return false;
	return true;
}
bool whilest(){
	char c[10000];
	fgets(c,10000,k1);
	if(!keysym(c,"symbol\0","(\0"))return false;
	if(!exp()) return false;
	strcpy(c,del1);
	if(!keysym(c,"symbol\0",")\0"))return false;
	fgets(c,10000,k1);
	if(!keysym(c,"symbol\0","{\0"))return false;
	fgets(c,10000,k1);
	if(strstr(c,"<keyword>let</keyword>\n")||strstr(c,"<keyword>while</keyword>\n")||strstr(c,"<keyword>if</keyword>\n")||strstr(c,"<keyword>do</keyword>\n")||strstr(c,"<keyword>return</keyword>\n")){
		fputs("<statements>\n",k2);
		k++;
		while(strstr(c,"<keyword>let</keyword>\n")||strstr(c,"<keyword>while</keyword>\n")||strstr(c,"<keyword>if</keyword>\n")||strstr(c,"<keyword>do</keyword>\n")||strstr(c,"<keyword>return</keyword>\n")){
			if(strstr(c,"<keyword>let</keyword>\n")){
				fputs("<letstatement>\n",k2);
				fputs(c,k2);
				if(!letst())return false;
				fputs("</letstatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>while</keyword>\n")){
				fputs("<whilestatement>\n",k2);
				fputs(c,k2);
				if(!whilest())return false;
				fputs("</whilestatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>if</keyword>\n")){
				fputs("<ifstatement>\n",k2);
				fputs(c,k2);
				if(!ifst())return false;
				fgets(c,10000,k1);
				if(strstr("<keyword>else</keyword>\n",c)){
					fputs(c,k2);
					if(!elsest())return false;
					fgets(c,10000,k1);
				}
				fputs("</ifstatement>\n",k2);
			}
			else if(strstr(c,"<keyword>do</keyword>\n")){
				fputs("<dostatement>\n",k2);
				fputs(c,k2);
				if(!dost())return false;
				fputs("</dostatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>return</keyword>\n")){
				fputs("<returnstatement>\n",k2);
				fputs(c,k2);
				if(!returnst())return false;
				fputs("</returnstatement>\n",k2);
				fgets(c,10000,k1);
			}
		}
		fputs("</statements>\n",k2);
	}
	if(!keysym(c,"symbol\0","}\0"))return false;
	return true;
}
bool dost(){
	char c[10000];
	if(!subrcall())return false;
	fgets(c,10000,k1);
	if(!keysym(c,"symbol\0",";\0"))return false;
	return true;
}
bool returnst(){
	char c[10000],a[10000];
	fgets(c,10000,k1);
	if(!strstr(c,"<symbol>;</symbol>\n")){
		if(!exp(c))return false;
		strcpy(a,del1);
	}
	if(!keysym(c,"symbol\0",";\0"))return false;
	return true;
}
bool keysym(char a[10000],char ks[10000],char na[10000]){
	char *te=ks;
	int i=1;
	while(a[i]!='>'){
		if(a[i]!=*te){
			fprintf(err,"Expecting %s but %s.",ks,tokbok(na));
 			return false;
		}
		i++;
		te++;
	}
	te=na;
	i++;
	while(a[i]!='<'){
		if(a[i]!=*te){
			fprintf(err,"%s",na);
			return false;
		}
		i++;
		te++;
	}
	fputs(a,k2);
	return true;
}

bool clanam(char*a){
	if(!strstr(substring(a,0,11),"<identifier>")){
		fprintf(err,"Expecting <identifier> but %s.",tokbok(a));
		return false;
	} 
	if(a[12]=='0'||a[12]=='1'||a[12]=='2'||a[12]=='3'||a[12]=='4'||a[12]=='5'||a[12]=='6'||a[12]=='7'||a[12]=='8'||a[12]=='9'){
		fputs("Invalid variable name.",err);
		return false;
	} 
	fputs(a,k2);
	return true;
}
char* tokbok(char buff[]){
	char* qp,*rp,*pp=(char*)malloc(10000*sizeof(char));
	rp=strstr(buff,">");
	rp++;
	qp=strstr(buff,"</");
	int i=0;
	while(rp!=qp) {
		pp[i]=*rp;
		i++;
		rp++;
	}
	rp[i]='\0';
	return pp;
}
bool sidentidec(char* ki,char* ty){
	char a[10000];
	fgets(a,10000,k1);
	if(!strstr(substring(a,0,11),"<identifier>")){
		fprintf(err,"Expecting <identifier> but %s.",tokbok(a));
		return false;
	} 
	if(a[12]=='0'||a[12]=='1'||a[12]=='2'||a[12]=='3'||a[12]=='4'||a[12]=='5'||a[12]=='6'||a[12]=='7'||a[12]=='8'||a[12]=='9'){
		fputs("Invalid variable name.",err);
		return false;
	}
		
		node ne;
		strcpy(ne.name,substring(a,12,strlen(a)-15));
		strcpy(ne.kind,ki);
		if(strstr(ty,"<identifier>"))
			strcpy(ne.type,substring(ty,12,strlen(ty)-15));
		else
			strcpy(ne.type,substring(ty,9,strlen(ty)-12));
		if(strstr(ki,"argument")){
			ne.index=vs[vs.size()-1].ac;
			vs[vs.size()-1].ac++;
		}
		else{
			ne.index=vs[vs.size()-1].lc;
			vs[vs.size()-1].lc++;
		}
		vs[vs.size()-1].sv.push_back(ne);
	fputs(a,k2);	
	//cout<<"bye"<<endl;
	return true;
}
bool cidentidec(char kin[],char ty[] ){
	char a[10000];
	fgets(a,10000,k1);
	if(!strstr(substring(a,0,11),"<identifier>")){
		fprintf(err,"Expecting <identifier> but %s.",tokbok(a));
		return false;
	}
	if(a[12]=='0'||a[12]=='1'||a[12]=='2'||a[12]=='3'||a[12]=='4'||a[12]=='5'||a[12]=='6'||a[12]=='7'||a[12]=='8'||a[12]=='9'){
		fputs("Invalid variable name.",err);
		return false;
	}

		node ne;
		strcpy(ne.name,substring(a,12,strlen(a)-15));
		strcpy(ne.kind,substring(kin,9,strlen(ty)-10));
		if(strstr(ty,"<identifier>"))
			strcpy(ne.type,substring(ty,12,strlen(ty)-15));
		else
			strcpy(ne.type,substring(ty,9,strlen(ty)-12));
		if(strstr("static",kin)){
		 	ne.index=xy.sc;
		 	xy.sc++;
		 }
		 else{
			ne.index=xy.fc;
		 	xy.fc++;
		 }
		 xy.cv.push_back(ne);
	fputs(a,k2);	
	return true;
}
bool type(char a[10000]){
	if(strstr(a,"<keyword>int</keyword>")||strstr(a,"<keyword>char</keyword>")||strstr(a,"<keyword>boolean</keyword>")||strstr(a,"<identifier>")) {
		fputs(a,k2);
		return true;
	}
	fprintf(err,"Expecting <keyword> but %s.",tokbok(a));
	return false;
}
bool classvardec(char bel[10000]){
	char a[10000],b[10000];
	fputs(bel,k2);
	fgets(a,10000,k1);
	if(type(a)){}
	else return false;
	if(!cidentidec(bel,a)) return false;
	fgets(b,10000,k1);
	while(strstr(b,"<symbol>,</symbol>\n")){
		fputs(b,k2);
		if(!cidentidec(bel,a)) return false;
		fgets(b,10000,k1);
	}
	if(!keysym(b,"symbol\0",";\0")) return false;
	return true;
}
bool subrname(char a[10000],char b[10000]){
	if(!strstr("<identifier>",substring(a,0,11))){
		fprintf(err,"Expecting <identifier> but %s.",tokbok(a));
		return false;
	}
	 srtab lat;
	 strcpy(lat.fun,substring(a,12,strlen(a)-15));
	 strcpy(lat.funtype,substring(b,9,strlen(b)-12));
	 vs.push_back(lat);
	fputs(a,k2);
	return true;
}
bool subbod(){
	char c[10000],b[10000];
	fputs("<subroutinebody>\n",k2);
	fgets(c,10000,k1);
	if(!keysym(c,"symbol\0","{\0"))return false;
	fgets(c,10000,k1);
	if(strstr(c,"<keyword>var</keyword>\n")){
		while(strstr(c,"<keyword>var</keyword>\n")){
			fputs("<vardec>\n",k2);
			fputs(c,k2);
			char a[10000];
			fgets(a,10000,k1);
			if(!type(a))return false;
			if(!sidentidec("local",a))return false;
			fgets(b,10000,k1);
			while(strstr(b,"<symbol>,</symbol>\n")){
				fputs(b,k2);
				if(!sidentidec("local",a))return false;
				fgets(b,10000,k1);
			}
			if(!keysym(b,"symbol\0",";\0"))return false;
			fgets(c,10000,k1);
			fputs("</vardec>\n",k2);
		}
	}
	if(strstr(c,"<keyword>let</keyword>\n")||strstr(c,"<keyword>while</keyword>\n")||strstr(c,"<keyword>if</keyword>\n")||strstr(c,"<keyword>do</keyword>\n")||strstr(c,"<keyword>return</keyword>\n")){
		fputs("<statements>\n",k2);
		while(strstr(c,"<keyword>let</keyword>\n")||strstr(c,"<keyword>while</keyword>\n")||strstr(c,"<keyword>if</keyword>\n")||strstr(c,"<keyword>do</keyword>\n")||strstr(c,"<keyword>return</keyword>\n")){
			if(strstr(c,"<keyword>let</keyword>\n")){
				fputs("<letstatement>\n",k2);
				fputs(c,k2);
				if(!letst())return false;
				fputs("</letstatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>while</keyword>\n")){
				fputs("<whilestatement\n",k2);
				fputs(c,k2);
				if(!whilest())return false;
				fputs("</whilestatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>if</keyword>\n")){
				fputs("<ifstatement>\n",k2);
				fputs(c,k2);
				if(!ifst())return false;
				fgets(c,10000,k1);
				if(strstr("<keyword>else</keyword>\n",c)){
					fputs(c,k2);
					if(!elsest())return false;
					fgets(c,10000,k1);
				}
				fputs("</ifstatement>\n",k2);
			}
			else if(strstr(c,"<keyword>do</keyword>\n")){
				fputs("<dostatement>\n",k2);
				fputs(c,k2);
				if(!dost())return false;
				fputs("</dostatement>\n",k2);
				fgets(c,10000,k1);
			}
			else if(strstr(c,"<keyword>return</keyword>")){
				fputs("<returnstatement>\n",k2);
				fputs(c,k2);
				if(!returnst())return false;
				fputs("</returnstatement>\n",k2);
				fgets(c,10000,k1);
			}
		}
		fputs("</statements>\n",k2);
	}
	if(!keysym(c,"symbol\0","}\0"))return false;
	fputs("</subroutinebody>\n",k2);
	return true;
}
bool subroutinedec(char* bel){
	char a[10000],b[10000],c[10000];
	fputs(bel,k2);
	fgets(a,10000,k1);
	if(strstr(a,"<keyword>void</keyword>\n")){
		fputs(a,k2);
	}
	else if(!type(a))return false;
	fgets(b,10000,k1);
	if(!subrname(b,bel)) return false;
	fgets(c,10000,k1);
	if(!keysym(c,"symbol\0","(\0"))return false;
	char* a1;
	fputs("<parameterlist>\n",k2);
	k++;
	fgets(c,10000,k1);
	if(!strstr(c,"<symbol>)</symbol>")){
		if(!type(c)) return false;
			char a1[10000];
			strcpy(a1,c);
			if(!sidentidec("argument",a1))return false;
			fgets(c,10000,k1);
		while(strstr(c,"<symbol>,</symbol>")){
			fputs(c,k2);
			fgets(c,10000,k1);
			if(!type(c)) return false;
			if(!sidentidec("argument",a1))return false;
			fgets(c,10000,k1);
			
		}
	}
	fputs("</parameterlist>\n",k2);
	if(!keysym(c,"symbol\0",")\0"))return false;
	if(!subbod()) return false;
	return true;
}
bool checkclass(){
	char be[10000];
	fputs("<class>\n",k2);
	fgets(be,10000,k1);
	 if(!keysym(be,"keyword\0","class\0"))return false;
	 fgets(be,10000,k1);
	 if(!clanam(be)) return false;
	 fgets(be,10000,k1);
	 if(!keysym(be,"symbol\0","{\0")) return false;
	fgets(be,10000,k1);
	if(strstr(be,"<keyword>static</keyword>\n")||strstr(be,"<keyword>field</keyword>\n")){
		while(strstr(be,"<keyword>static</keyword>\n")||strstr(be,"<keyword>field</keyword>\n")){
		fputs("<classvardec>\n",k2);
			if(!classvardec(be))return false;
			fgets(be,10000,k1);
			fputs("</classvardec>\n",k2);
		}
	}
	if(strstr(be,"<keyword>constructor</keyword>\n")||strstr(be,"<keyword>function</keyword>\n")||strstr(be,"<keyword>method</keyword>\n")){
		while(strstr(be,"<keyword>constructor</keyword>\n")||strstr(be,"<keyword>function</keyword>\n")||strstr(be,"<keyword>method</keyword>\n")){
			fputs("<subroutinedec>\n",k2);
			if(!subroutinedec(be))return false;
			fgets(be,10000,k1);
			fputs("</subroutinedec>\n",k2);
		}
	}
	if(!keysym(be,"symbol\0","}\0")) return false;
	fputs("</class>\n",k2);
	return true;
}
void compilesubroutinedeclaration();
void compilestatements();
void compileexpression();
void compileterm();
int compileexpressionlist();
void compileletstatement(){
	int i;
	fgets(prob,10000,k1);
	for(i=0;i<vs[subr].sv.size();i++){
		if(!strcmp(substring(prob,12,strlen(prob)-15),vs[subr].sv[i].name)) break;
	}
	if(i!=vs[subr].sv.size()){
		fgets(prob,10000,k1);
		if(strstr(prob,"<symbol>[")){
			fgets(prob,10000,k1);
			if(strstr(prob,"<expression>")){
				compileexpression();
			}
			fgets(prob,10000,k1);
			fprintf(k2,"push %s %d\nadd\n","this",vs[subr].sv[i].index);
			fgets(prob,10000,k1);
		}
		fgets(prob,10000,k1);
		if(strstr(prob,"<expression>")){
			compileexpression();
		}
		fprintf(k2,"pop %s %d\n",vs[subr].sv[i].kind,vs[subr].sv[i].index);	
		fgets(prob,10000,k1);
	}
	else{
		for(int i=0;i<xy.cv.size();i++){
			if(!strcmp(substring(prob,12,strlen(prob)-15),xy.cv[i].name)) break;
		}
		fgets(prob,10000,k1);
		if(strstr(prob,"<symbol>[")){
			fgets(prob,10000,k1);
			if(strstr(prob,"<expression>")){
				compileexpression();
			}
			fgets(prob,10000,k1);
			cout<<"yo";
			fprintf(k2,"push %s %d\nadd\n","this",vs[subr].sv[i].index);
			fgets(prob,10000,k1);
		}
		fgets(prob,10000,k1);
		if(strstr(prob,"<expression>")){
			compileexpression();
		}
		cout<<"yo";
		fprintf(k2,"pop %s %d\n","this",vs[subr].sv[i].index);	
		fgets(prob,10000,k1);
	}

	fgets(prob,10000,k1);


}
void compileterm(){
	fgets(prob,10000,k1);
	if(strstr(prob,"<symbol>-")){
		fgets(prob,10000,k1);
		compileterm();
		fprintf(k2,"neg\n");
		fgets(prob,10000,k1);

	}
	if(strstr(prob,"<symbol>~")){
		fgets(prob,10000,k1);
		compileterm();
		fprintf(k2,"not\n");
		fgets(prob,10000,k1);

	}
	if(strstr(prob,"<symbol>(")){
		fgets(prob,10000,k1);
		compileexpression();
		fgets(prob,10000,k1);
		fgets(prob,10000,k1);

	}
	if(strstr(prob,"<integerconstant>")){
		fprintf(k2,"push constant %s\n",tokbok(prob));
		fgets(prob,10000,k1);

	}
	if(strstr(prob,"<stringconstant>")){
		fprintf(k2,"push constant %d\ncall String.new 1\n",strlen(tokbok(prob)));
		for(int i=0;i<strlen(tokbok(prob));i++){
			fprintf(k2,"push constant %d\ncall String.appendChar 2\n",i);
		}
		fgets(prob,10000,k1);

	}
	if(strstr(prob,"false")||strstr(prob,"null")){
		fprintf(k2,"push constant 0\n");
		fgets(prob,10000,k1);

	}
	if(strstr(prob,"true")){
		fprintf(k2,"push constant 0\nnot\n");
		fgets(prob,10000,k1);

	}
	if(strstr(prob,"this")){
		fprintf(k2,"push pointer 0\nnot\n");
		fgets(prob,10000,k1);

	}
	if(strstr(prob,"<identifier>")){
		int ind;
		char kas[10000];
		int i;
		for( i=0;i<vs[subr].sv.size();i++){
			if(!strcmp(substring(prob,12,strlen(prob)-15),vs[subr].sv[i].name)){
				strcpy(kas,vs[subr].sv[i].kind);
				ind=vs[subr].sv[i].index;
				break;
			}

		}
		if(i==vs[subr].sv.size()){
			for(int i=0;i<xy.cv.size();i++){
				if(!strcmp(substring(prob,12,strlen(prob)-15),xy.cv[i].name)){
					strcpy(kas,xy.cv[i].kind);
					ind=xy.cv[i].index;
					break;
				} 
			}
		}
		fgets(prob,10000,k1);
		if(strstr(prob,"<symbol>[")){
			fgets(prob,10000,k1);
			compileexpression();
			fgets(prob,10000,k1);
			fprintf(k2,"push %s %d\nadd\npop pointer 1\npush that 0\n",kas,ind);
			fgets(prob,10000,k1);
		}
		else if(strstr(prob,"<symbol>(")||strstr(prob,"<symbol>.")){
			int i,j,fg,flag3=0;
			fgets(prob,10000,k1);
			char id1[10000],id2[10000],id1t[10000];
			fgets(prob,10000,k1);
			strcpy(id1,substring(prob,12,strlen(prob)-15));
			fgets(prob,10000,k1);
			if(strstr(prob,"<symbol>.")){
				fgets(prob,10000,k1);
				strcpy(id2,substring(prob,12,strlen(prob)-15));
				for(i=0;i<vs[subr].sv.size();i++){
					if(!strcmp(id1,vs[subr].sv[i].name)){
						fprintf(k2,"push %s %d\n",vs[subr].sv[i].kind,vs[subr].sv[i].index);
						strcpy(id1t,vs[subr].sv[i].type);
						flag3=1;
						break;
					}
				}
				if(i==vs[subr].sv.size()){
					for(j=0;j<xy.cv.size();j++){
						if(!strcmp(id1,xy.cv[j].name)){
							fprintf(k2,"push %s %d\n",xy.cv[j].kind,xy.cv[j].index);
							strcpy(id1t,xy.cv[j].type);
							flag3=1;
						}
					}
				}
				fgets(prob,10000,k1);
				fgets(prob,10000,k1);
				if(strstr(prob,"<expressionlist>"))
					fg=compileexpressionlist();
				fgets(prob,10000,k1);
				fgets(prob,10000,k1);
				if(flag3==0){
					fprintf(k2,"call %s.%s %d\n",id1,id2,fg);
				}
				else{
					fprintf(k2,"call %s.%s %d\n",id1t,id2,fg);
				}

			}
			else{
				fprintf(k2,"push pointer 0\n");
				fgets(prob,10000,k1);
				if(strstr(prob,"<expressionlist>"))
					fg=compileexpressionlist();
				fgets(prob,10000,k1);
				fgets(prob,10000,k1);
				fprintf(k2,"call %s.%s %d\n",curclass,id1,fg+1);
			}
			fgets(prob,10000,k1);
		}
		else{
			fprintf(k2,"push %s %d",kas,ind);
		}
	}

}
void compileexpression(){
	fgets(prob,10000,k1);
	while(!strstr(prob,"</expression>")){
		compileterm();
		fgets(prob,10000,k1);
		if(strstr(prob,"+"))fprintf(k2,"add\n");
		if(strstr(prob,"-"))fprintf(k2,"sub\n");
		if(strstr(prob,"&"))fprintf(k2,"and\n");
		if(strstr(prob,"|"))fprintf(k2,"or\n");
		if(strstr(prob,">><"))fprintf(k2,"gt\n");
		if(strstr(prob,"><<"))fprintf(k2,"lt\n");
		if(strstr(prob,"="))fprintf(k2,"eq\n");
		if(strstr(prob,"*"))fprintf(k2,"call Math.multiply 2\n");
		if(strstr(prob,"/"))fprintf(k2,"call Math.divide 2\n");
		if(strstr(prob,"</expression>"))break;
		fgets(prob,10000,k1);
	}
	fgets(prob,10000,k1);
}
int compileexpressionlist(){
	int fg=0;
	fgets(prob,10000,k1);
	while(!strstr(prob,"</expressionlist>")){
		compileexpression();
		fg++;
		fgets(prob,10000,k1);
		if(strstr(prob,"<symbol>,"))
			fgets(prob,10000,k1);
	}
	return fg;
}
void compilereturnstatement(){
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	if(strstr(prob,"<expression>")){
		compileexpression();
		fprintf(k2,"return\n");
		fgets(prob,10000,k1);
	}
	else{
		fprintf(k2,"push constant 0\nreturn\n");
	}
	fgets(prob,10000,k1);
}


void compiledostatement(){
	int i,j,fg,flag3=0;
	fgets(prob,10000,k1);
	char id1[10000],id2[10000],id1t[10000];
	fgets(prob,10000,k1);
	strcpy(id1,substring(prob,12,strlen(prob)-15));
	fgets(prob,10000,k1);
	if(strstr(prob,"<symbol>.")){
		fgets(prob,10000,k1);
		strcpy(id2,substring(prob,12,strlen(prob)-15));
		for(i=0;i<vs[subr].sv.size();i++){
			if(!strcmp(id1,vs[subr].sv[i].name)){
				fprintf(k2,"push %s %d\n",vs[subr].sv[i].kind,vs[subr].sv[i].index);
				strcpy(id1t,vs[subr].sv[i].type);
				flag3=1;
				break;
			}
		}
		if(i==vs[subr].sv.size()){
			for(j=0;j<xy.cv.size();j++){
				if(!strcmp(id1,xy.cv[j].name)){
					fprintf(k2,"push %s %d\n",xy.cv[j].kind,xy.cv[j].index);
					strcpy(id1t,xy.cv[j].type);
					flag3=1;
				}
			}
		}
		fgets(prob,10000,k1);
		fgets(prob,10000,k1);
		if(strstr(prob,"<expressionlist>"))
			fg=compileexpressionlist();
		fgets(prob,10000,k1);
		fgets(prob,10000,k1);
		if(flag3==0){
			fprintf(k2,"call %s.%s %d\npop temp 0\n",id1,id2,fg);
		}
		else{
			fprintf(k2,"call %s.%s %d\npop temp 0\n",id1t,id2,fg);
		}

	}
	else{
		fprintf(k2,"push pointer 0\n");
		fgets(prob,10000,k1);
		if(strstr(prob,"<expressionlist>"))
			fg=compileexpressionlist();
		fgets(prob,10000,k1);
		fgets(prob,10000,k1);
		fprintf(k2,"call %s.%s %d\npop temp 0\n",curclass,id1,fg+1);
	}
	fgets(prob,10000,k1);

}
void compilewhilestatement(){
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	int tlabelnum=labelname;
	labelname=labelname+2;
	fprintf(k2,"label %s.%d\n",curclass,tlabelnum);
	fgets(prob,10000,k1);
	if(strstr(prob,"<expression>")){
		compileexpression();
	}
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	fprintf(k2,"not\nif-goto %s.%d\n",curclass,tlabelnum+1);
	fgets(prob,10000,k1);
	compilestatements();
	fgets(prob,10000,k1);
	fprintf(k2,"goto %s.%d\nlabel %s.%d\n",curclass,tlabelnum,curclass,tlabelnum+1);
	fgets(prob,10000,k1);
}
void compileifstatement(){
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	int tlabelnum=labelname;
	labelname=labelname+2;
	fgets(prob,10000,k1);
	if(strstr(prob,"<expression>")){
		compileexpression();
	}
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	cout<<"hi";
	fprintf(k2,"not\nif-goto %s.%d\n",curclass,tlabelnum);
	fgets(prob,10000,k1);
	compilestatements();
	fgets(prob,10000,k1);
	fprintf(k2,"goto %s.%d\nlabel %s.%d\n",curclass,tlabelnum+1,curclass,tlabelnum);
	fgets(prob,10000,k1);
	if(strstr(prob,">else<")){
		fgets(prob,10000,k1);
		fgets(prob,10000,k1);
		compilestatements();
		fgets(prob,10000,k1);
		fgets(prob,10000,k1);
	}
	fprintf(k2,"label %s.%d",curclass,tlabelnum+1);

}
void compilestatements(){
	fgets(prob,10000,k1);
	while(!strstr(prob,"</statements>")){
		if(strstr(prob,"<letstatement>"))
			compileletstatement();
		if(strstr(prob,"<ifstatement>"))
			compileifstatement();
		if(strstr(prob,"<whilestatement>"))
			compilewhilestatement();
		if(strstr(prob,"<dostatement>"))
			compiledostatement();
		if(strstr(prob,"<returnstatement>"))
			compilereturnstatement();
		fgets(prob,10000,k1);
	}
}
void compilevardec(){
	fgets(prob,10000,k1);
	while(!strstr(prob,"</vardec>"))
		fgets(prob,10000,k1);
	fgets(prob,10000,k1);
}
void compilesubroutinebody(){
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	while(strstr(prob,"<vardec>")){
		compilevardec();
	}
	fgets(prob,10000,k1);
	fprintf(k2,"function %s.%s %d\n",curclass,vs[subr].fun,vs[subr].lc);
	if(strstr(vs[subr].funtype,"constructor")){
		fprintf(k2,"push constant %d\n",xy.fc);
		fprintf(k2,"Call Memory.alloc 1\npop pointer 0\n");
	}
	if(strstr(vs[subr].funtype,"method")){
		fprintf(k2,"push argument 0\npop pointer 0\n");
	}
	compilestatements();
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
}
void compileparameterlist(){
	fgets(prob,10000,k1);
	while(!strstr(prob,"</parameterlist>"))
		fgets(prob,10000,k1);
	return;
}
void compilesubroutinedeclaration(){
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	if(strstr(vs[subr].funtype,"method")){
		node ne;
		strcpy(ne.name,"this");
		strcpy(ne.kind,"argument");
		strcpy(ne.type,curclass);
		ne.index=0;
		vs[subr].sv.push_back(ne);
		vs[subr].ac++;
	}
	if(strstr(prob,"<parameterlist>")){
		compileparameterlist();
	}
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	if(strstr(prob,"<subroutinebody>")){
		compilesubroutinebody();
	}
	fgets(prob,10000,k1);

}
void compileclassvardec(){
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	while(strstr(prob,"<symbol>,")){
		fgets(prob,10000,k1);
	}
	fgets(prob,10000,k1);
	return;
}
void compileclass(){
	subr=0;
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	strcpy(curclass,substring(prob,12,strlen(prob)-15));
	fgets(prob,10000,k1);
	fgets(prob,10000,k1);
	while(strstr(prob,"<classvardec>")){
		compileclassvardec();
		//compile class var dec ends with closing tag
		fgets(prob,10000,k1);
	}
	while(strstr(prob,"<subroutinedec>")){

		compilesubroutinedeclaration();
		fgets(prob,10000,k1);
		subr++;
	}
	fgets(prob,10000,k1);
	return;
}
main(int argc,char* argv[]){
	int t;
	cin>>t;
	tabv.resize(1);
	non=1;
	for(int i=1;i<=t;i++){
		fname.push_back(substring(argv[i],0,strlen(argv[i])-6));
	}
	err=fopen("compile.err","w");
	for(int xyz=0;xyz<t;xyz++){
	FILE *p1,*p2,*p3;
	int c=0;
	int pl=0,vs1=1;
	//opening files
	p1=fopen(argv[non],"r");
	p2=fopen("test.ir","w");
	char b[100];
	char p[100];
	//using fgets on asm file into buffer b till feof
	while(fgets(b,100,p1)){
		int w=0;
		while(b[w]==' ') w++;
		//checking each character in b for unwanted values like comments, space, etc..
		int i;
		for(i=w,k=0;i<100;i++){
			if(b[i]=='\n'||b[i]=='\r') break;
			if(i!=0&&(b[i-1]==' ')&&(b[i]==' ')) continue;
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
	p2=fopen("test.ir","r");
	p3=fopen("temp.tok","w");
	fputs("<tokens>\n",p3);
	char c1='a';
	while(c1<128){
		if(c1>128||c1<0) break;
		int s=0;
		char buff[10000],*h;
		int i=0;
		c1=fgetc(p2);
		if(c1==' '||c1=='\t'||c1=='\n'||c1=='\0') 
			continue;
		if(c1=='{'||c1=='}'||c1=='('||c1==')'||c1=='['||c1==']'||c1=='.'||c1==','||c1==';'||c1=='+'||c1=='-'||c1=='*'||c1=='/'||c1=='&'||c1=='|'||c1=='<'||c1=='>'||c1=='='||c1=='~')
			fprintf(p3,"<symbol>%c</symbol>\n",c1);
		while(i<10000&&((s==0&&(c1!=' '&&c1!='\t'&&c1!='\n'&&c1!='\0'))||(s==1&&c1!='"'))){
			if(c1=='{'||c1=='}'||c1=='('||c1==')'||c1=='['||c1==']'||c1=='.'||c1==','||c1==';'||c1=='+'||c1=='-'||c1=='*'||c1=='/'||c1=='&'||c1=='|'||c1=='<'||c1=='>'||c1=='='||c1=='~')break;
			if(c1=='"')s=1;
			else{
				buff[i]=c1;
				i++;
			}
			c1=fgetc(p2);
		}
		if(c1>128||c1<0) break;
		buff[i]='\0';
		if(strlen(buff)==0)continue;
		if(s==1){
			fprintf(p3,"<%s>%s</%s>\n","stringconstant",buff,"/stringconstant");
			s=0;
			continue;
		} 
		h=recognise(buff);
		fprintf(p3,"<%s>%s</%s>\n",h,buff,h);
		if(c1=='{'||c1=='}'||c1=='('||c1==')'||c1=='['||c1==']'||c1=='.'||c1==','||c1==';'||c1=='+'||c1=='-'||c1=='*'||c1=='/'||c1=='&'||c1=='|'||c1=='<'||c1=='>'||c1=='='||c1=='~')
		fprintf(p3,"<symbol>%c</symbol>\n",c1);
	}
	fputs("</tokens>\n",p3);
	fclose(p2);
	fclose(p3);
	k1=fopen("temp.tok","r");
	k2=fopen(argv[t+non],"w");
	char buff[10000];
	fgets(buff,10000,k1);
	bool h1=false;
	k=0;
	if(!strcmp(buff,"<tokens>\n")){
		h1=checkclass();
	}
	else{
		fputs("Expected token tag.\n",err);
		return 0;
	} 
	cout<<h1;
	if(!h1) return 0;
	fclose(k2);
	fclose(k1);
	labelname=0;
	k1=fopen(argv[t+non],"r");
	k2=fopen(argv[2*t+non],"w");
	fgets(prob,10000,k1);
	if(strstr(prob,"class"))
		compileclass();
	fgets(prob,10000,k1);
	fclose(k2);
	fclose(k1);
	vs.clear();
	xy.cv.clear();
	xy.fc=0;
	xy.sc=0;
	non++;
}


}