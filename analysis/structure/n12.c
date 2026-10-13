#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
static uint8_t *d1; static int32_t *TE,*TC,*TS; static long I0;
static void *loadf(const char *f){FILE*fp=fopen(f,"rb");fseek(fp,0,SEEK_END);size_t sz=ftell(fp);fseek(fp,0,SEEK_SET);void*p=malloc(sz);if(fread(p,1,sz,fp)!=sz)exit(1);fclose(fp);return p;}
static inline long nxt(long i,int m){long e=i/(2187L*495),c=(i/495)%2187,s=i%495;return ((long)TE[e*18+m]*2187+TC[c*18+m])*495+TS[s*18+m];}
static long cnt; 
static void dfs(long i,int rem,int last){
  if(rem==0){ if(i==I0) cnt++; return; }
  for(int m=0;m<18;m++){int f=m/3; if(last>=0&&(f==last||(f%3==last%3&&f<last))) continue;
    long j=nxt(i,m); if(d1[j]>rem-1) continue; dfs(j,rem-1,f);}
}
int main(int argc,char**argv){
  int fd=open("/root/inter/k1dist.bin",O_RDONLY); struct stat st; fstat(fd,&st);
  d1=mmap(0,st.st_size,PROT_READ,MAP_SHARED,fd,0);
  TE=loadf("/root/f28/TE.bin");TC=loadf("/root/f28/TC.bin");TS=loadf("/root/f28/TS.bin");
  FILE*f=fopen("/root/f28/I0.txt","r"); if(fscanf(f,"%ld",&I0)!=1) return 1;
  int L=atoi(argv[1]); long x;
  while(scanf("%ld",&x)==1){ cnt=0; dfs(x,L,-1); printf("%ld %d %ld\n",x,d1[x],cnt); fflush(stdout);}
}
