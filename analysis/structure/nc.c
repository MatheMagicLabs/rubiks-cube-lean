#include "cube.h"
static uint64_t nodes;
static void dfs(const cube*c,int n){ nodes++; if(n==0) return; if(cdist[cornerIdx(c)]>n) return;
  for(int m=0;m<18;m++){cube y; mul(c,&MV[m],&y); dfs(&y,n-1);} }
int main(){initmoves(); buildCorner(); dfs(&ID,9); printf("nodes %llu\n",(unsigned long long)nodes);}
