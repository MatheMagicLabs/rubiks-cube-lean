#include "cube.h"
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
static int lcm(int a,int b){return a/gcd(a,b)*b;}
static int order(const cube*c){
  int o=1, seen[12]={0};
  for(int i=0;i<8;i++) if(!seen[i]){int L=0,t=0,j=i; while(!seen[j]){seen[j]=1;t+=c->co[j];j=c->cp[j];L++;} o=lcm(o, t%3?3*L:L);}
  memset(seen,0,sizeof seen);
  for(int i=0;i<12;i++) if(!seen[i]){int L=0,t=0,j=i; while(!seen[j]){seen[j]=1;t+=c->eo[j];j=c->ep[j];L++;} o=lcm(o, t%2?2*L:L);}
  return o;
}
static int best[1261]; static int ex[1261][16]; static int path[16]; static int maxd;
static void dfs(const cube*c,int d,int lastf){
  if(d>0){int o=order(c); if(best[o]>d){best[o]=d; memcpy(ex[o],path,sizeof path);}}
  if(d==maxd) return;
  for(int f=0;f<6;f++){ if(!allowed(lastf,f)) continue;
    for(int k=0;k<3;k++){ cube y; mul(c,&MV[3*f+k],&y); path[d]=3*f+k; dfs(&y,d+1,f);} }
}
int main(int argc,char**argv){
  initmoves(); maxd=atoi(argv[1]); for(int i=0;i<1261;i++) best[i]=99;
  dfs(&ID,0,-1);
  const char*F="URFDLB"; const char*P[3]={"","2","'"};
  for(int o=1;o<=1260;o++) if(best[o]<99){ printf("%d %d :",o,best[o]); for(int k=0;k<best[o];k++) printf(" %c%s",F[ex[o][k]/3],P[ex[o][k]%3]); printf("\n"); }
}
