#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef struct { unsigned char cp[8],co[8],ep[12],eo[12]; } cube;
static const unsigned char MCP[6][8]={{3,0,1,2,4,5,6,7},{4,1,2,0,7,5,6,3},{1,5,2,3,0,4,6,7},{0,1,2,3,5,6,7,4},{0,2,6,3,4,1,5,7},{0,1,3,7,4,5,2,6}};
static const unsigned char MCO[6][8]={{0},{2,0,0,1,1,0,0,2},{1,2,0,0,2,1,0,0},{0},{0,1,2,0,0,2,1,0},{0,0,1,2,0,0,2,1}};
static const unsigned char MEP[6][12]={{3,0,1,2,4,5,6,7,8,9,10,11},{8,1,2,3,11,5,6,7,4,9,10,0},{0,9,2,3,4,8,6,7,1,5,10,11},{0,1,2,3,5,6,7,4,8,9,10,11},{0,1,10,3,4,5,9,7,8,2,6,11},{0,1,2,11,4,5,6,10,8,9,3,7}};
static const unsigned char MEO[6][12]={{0},{0},{0,1,0,0,0,1,0,0,1,1,0,0},{0},{0},{0,0,0,1,0,0,0,1,0,0,1,1}};
static cube MV[18], ID;
static void mul(const cube*a,const cube*b,cube*r){
  for(int i=0;i<8;i++){r->cp[i]=a->cp[b->cp[i]]; r->co[i]=(a->co[b->cp[i]]+b->co[i])%3;}
  for(int i=0;i<12;i++){r->ep[i]=a->ep[b->ep[i]]; r->eo[i]=(a->eo[b->ep[i]]+b->eo[i])&1;}
}
static void initmoves(void){
  for(int i=0;i<8;i++){ID.cp[i]=i;ID.co[i]=0;} for(int i=0;i<12;i++){ID.ep[i]=i;ID.eo[i]=0;}
  for(int f=0;f<6;f++){cube b; memcpy(b.cp,MCP[f],8);memcpy(b.co,MCO[f],8);memcpy(b.ep,MEP[f],12);memcpy(b.eo,MEO[f],12);
    cube x=b; for(int k=0;k<3;k++){MV[3*f+k]=x; cube y; mul(&x,&b,&y); x=y;}}
}
static uint32_t cornerIdx(const cube*c){
  uint32_t r=0; for(int i=0;i<8;i++){int s=0; for(int j=i+1;j<8;j++) if(c->cp[j]<c->cp[i]) s++; r=r*(8-i)+s;}
  uint32_t t=0; for(int i=0;i<7;i++) t=t*3+c->co[i]; return r*2187+t;
}
static void cornerDec(uint32_t x,cube*c){
  uint32_t t=x%2187, r=x/2187; int s=0;
  for(int i=6;i>=0;i--){c->co[i]=t%3; s+=c->co[i]; t/=3;} c->co[7]=(3-s%3)%3;
  int lehm[8]; for(int i=7;i>=0;i--){lehm[i]=r%(8-i); r/=(8-i);}
  int used[8]={0}; for(int i=0;i<8;i++){int k=lehm[i]; for(int j=0;j<8;j++) if(!used[j]){ if(k==0){c->cp[i]=j;used[j]=1;break;} k--; }}
}
#define NC 88179840u
static unsigned char *cdist;
static void buildCorner(void){
  FILE*f=fopen("/root/explore/c/cdist.bin","rb");
  cdist=malloc(NC);
  if(f){ if(fread(cdist,1,NC,f)!=NC) exit(1); fclose(f); return; }
  memset(cdist,255,NC); cdist[cornerIdx(&ID)]=0;
  for(int d=0;;d++){ uint64_t n=0;
    for(uint32_t x=0;x<NC;x++) if(cdist[x]==d){ cube c; cornerDec(x,&c); for(int i=0;i<12;i++){c.ep[i]=i;c.eo[i]=0;}
      for(int m=0;m<18;m++){cube y; mul(&c,&MV[m],&y); uint32_t z=cornerIdx(&y); if(cdist[z]==255){cdist[z]=d+1;n++;}}}
    fprintf(stderr,"corner depth %d: %llu\n",d+1,(unsigned long long)n); if(!n) break; }
  f=fopen("/root/explore/c/cdist.bin","wb"); fwrite(cdist,1,NC,f); fclose(f);
}
/* canonical: next move face f allowed after last face l if f!=l and not (f is opposite of l with f<l) */
static int allowed(int l,int f){ if(l<0) return 1; if(f==l) return 0; if(f%3==l%3 && f<l) return 0; return 1; }
