#include "cube.h"
/* face indices: U0 R1 F2 D3 L4 B5; opposite pairs share f%3 */
static int maxd; static int path[32]; static uint64_t nodes, found11, found11x;
static FILE*out;
static void check(const cube*c){
  for(int i=0;i<8;i++) if(c->cp[i]!=i||c->co[i]) return;
  int seen[12]={0}, cyc=0, fixed=-1;
  for(int i=0;i<12;i++) if(!seen[i]){int L=0,j=i; while(!seen[j]){seen[j]=1;j=c->ep[j];L++;} if(L==11)cyc=1; if(L==1) fixed=i;}
  if(!cyc) return;
  found11x++;
  int ord11 = (c->eo[fixed]==0);
  if(ord11) found11++;
  if(1){ fprintf(out,"%d %d:",ord11,maxd); for(int k=0;k<maxd;k++) fprintf(out," %d",path[k]); fprintf(out,"\n"); }
}
static void dfs(const cube*c,int d,int lastf){
  nodes++;
  if(d==maxd){ check(c); return; }
  if(cdist[cornerIdx(c)]>maxd-d) return;
  for(int f=0;f<6;f++){ if(!allowed(lastf,f)) continue;
    for(int k=0;k<3;k++){ cube y; mul(c,&MV[3*f+k],&y); path[d]=3*f+k; dfs(&y,d+1,f);} }
}
int main(int argc,char**argv){
  initmoves(); buildCorner(); out=fopen(argv[2],"w");
  for(maxd=1;maxd<=atoi(argv[1]);maxd++){ nodes=found11=found11x=0; dfs(&ID,0,-1);
    printf("depth %d nodes %llu corners-solved&11-cycle %llu order-exactly-11 %llu\n",maxd,(unsigned long long)nodes,(unsigned long long)found11x,(unsigned long long)found11); fflush(stdout);
    if(found11) break; }
  fclose(out);
}
