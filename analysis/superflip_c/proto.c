// Prototype of a Lean-certifiable superflip search: canonical words, rotation-normalised first two moves,
// heuristic = max(phase-1 distance on 3 axes [Lean K1 table], corner distance [optionally 3 axes]).
#include "/root/explore/c/cube.h"
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <time.h>
static uint8_t *d1; static int32_t *TE,*TC,*TS; static long I0;
static int eoI[4096], coI[6561], sI[4096];
static int mu[3][18];
static cube S, Si;
static int USE_CORN=1, CORN3=0;
static void *loadf(const char *f){FILE*fp=fopen(f,"rb");fseek(fp,0,SEEK_END);size_t sz=ftell(fp);fseek(fp,0,SEEK_SET);void*p=malloc(sz);if(fread(p,1,sz,fp)!=sz)exit(1);fclose(fp);return p;}
static inline long nxt(long i,int m){long e=i/(2187L*495),c=(i/495)%2187,s=i%495;return ((long)TE[e*18+m]*2187+TC[c*18+m])*495+TS[s*18+m];}
static long rank1(const cube*x){int eb=0,cb=0,mb=0;
  for(int i=0;i<12;i++){eb|=x->eo[i]<<i; mb|=(x->ep[i]>=8)<<i;}
  for(int i=0;i<8;i++) cb=cb*3+x->co[i];
  return ((long)eoI[eb]*2187+coI[cb])*495+sI[mb];}
static void conj(const cube*x,cube*r){cube t; mul(&S,x,&t); mul(&t,&Si,r);}
static void inv(const cube*a,cube*r){for(int i=0;i<8;i++)r->cp[a->cp[i]]=i; for(int i=0;i<8;i++) r->co[i]=(3-a->co[r->cp[i]])%3;
  for(int i=0;i<12;i++)r->ep[a->ep[i]]=i; for(int i=0;i<12;i++) r->eo[i]=a->eo[r->ep[i]];}
static int isid(const cube*x){return memcmp(x,&ID,sizeof(cube))==0;}
static uint64_t nodes[32], evals; static int B, found;
static int h(const cube*x,const long*r){int v=d1[r[0]]; if(d1[r[1]]>v)v=d1[r[1]]; if(d1[r[2]]>v)v=d1[r[2]];
  if(USE_CORN){int c=cdist[cornerIdx(x)]; if(c>v)v=c;
    if(CORN3){cube y,z; conj(x,&y); c=cdist[cornerIdx(&y)]; if(c>v)v=c; conj(&y,&z); c=cdist[cornerIdx(&z)]; if(c>v)v=c;}}
  return v;}
static void dfs(const cube*x,const long*r,int g,int lastf){
  nodes[g]++;
  if(g==B){ if(isid(x)) found++; return; }
  for(int f=0;f<6;f++){ if(!allowed(lastf,f)) continue;
    if(g==0 && f!=0) continue;                 // first move: U face (rotation normalisation)
    if(g==1 && !(f==3||f==1)) continue;          // second move: D or R face (stabiliser of U)
    for(int k=0;k<3;k++){int m=3*f+k; cube y; mul(x,&MV[m],&y); long rr[3]; rr[0]=nxt(r[0],m); rr[1]=nxt(r[1],mu[1][m]); rr[2]=nxt(r[2],mu[2][m]);
      evals++; if(g+1+h(&y,rr)>B) continue; dfs(&y,rr,g+1,f);} } }
int main(int argc,char**argv){
  initmoves(); buildCorner();
  int fd=open("/root/inter/k1dist.bin",O_RDONLY); struct stat st; fstat(fd,&st);
  d1=mmap(0,st.st_size,PROT_READ,MAP_SHARED|MAP_POPULATE,fd,0);
  TE=loadf("/root/f28/TE.bin");TC=loadf("/root/f28/TC.bin");TS=loadf("/root/f28/TS.bin");
  FILE*f=fopen("/root/f28/I0.txt","r"); if(fscanf(f,"%ld",&I0)!=1) return 1;
  // coordinate dictionaries from the Lean listings
  memset(eoI,-1,sizeof eoI); memset(coI,-1,sizeof coI); memset(sI,-1,sizeof sI);
  f=fopen("/root/inter/eoL.txt","r"); for(int k=0;k<2048;k++){int b=0;for(int i=0;i<12;i++){int v;if(fscanf(f,"%d",&v)!=1)return 2;b|=v<<i;} eoI[b]=k;} fclose(f);
  f=fopen("/root/inter/coL.txt","r"); for(int k=0;k<2187;k++){int b=0;for(int i=0;i<8;i++){int v;if(fscanf(f,"%d",&v)!=1)return 3;b=b*3+v;} coI[b]=k;} fclose(f);
  f=fopen("/root/inter/mL.txt","r"); for(int k=0;k<495;k++){int b=0;for(int i=0;i<12;i++){int v;if(fscanf(f,"%d",&v)!=1)return 4;b|=v<<i;} sI[b]=k;} fclose(f);
  if(rank1(&ID)!=I0){printf("rank mismatch %ld %ld\n",rank1(&ID),I0);return 5;}
  // URF rotation
  unsigned char cp[8]={0,4,5,1,3,7,6,2},co[8]={1,2,1,2,2,1,2,1},ep[12]={1,8,5,9,3,11,7,10,0,4,6,2},eo[12]={1,0,1,0,1,0,1,0,1,1,1,1};
  memcpy(S.cp,cp,8);memcpy(S.co,co,8);memcpy(S.ep,ep,12);memcpy(S.eo,eo,12); inv(&S,&Si);
  for(int m=0;m<18;m++){mu[0][m]=m; cube c; conj(&MV[m],&c); int j=-1; for(int k=0;k<18;k++) if(!memcmp(&c,&MV[k],sizeof c)) j=k; mu[1][m]=j;}
  for(int m=0;m<18;m++) mu[2][m]=mu[1][mu[1][m]];
  // self-test: incremental ranks equal direct ranks on random walks
  srand(1); for(int t=0;t<1000;t++){cube x=ID; long r[3]={I0,I0,I0}; for(int s=0;s<30;s++){int m=rand()%18; cube y; mul(&x,&MV[m],&y); x=y; r[0]=nxt(r[0],m); r[1]=nxt(r[1],mu[1][m]); r[2]=nxt(r[2],mu[2][m]);}
    cube c1,c2; conj(&x,&c1); conj(&c1,&c2); if(r[0]!=rank1(&x)||r[1]!=rank1(&c1)||r[2]!=rank1(&c2)){printf("selftest fail\n");return 6;}}
  printf("selftest ok\n");
  // superflip
  cube sf=ID; for(int i=0;i<12;i++) sf.eo[i]=1;
  cube c1,c2; conj(&sf,&c1); conj(&c1,&c2); long r[3]={rank1(&sf),rank1(&c1),rank1(&c2)};
  printf("sf d1 axes: %d %d %d corner %d\n",d1[r[0]],d1[r[1]],d1[r[2]],cdist[cornerIdx(&sf)]);
  int from=atoi(argv[1]), to=atoi(argv[2]); USE_CORN=atoi(argv[3]); CORN3=atoi(argv[4]);
  for(B=from;B<=to;B++){ memset(nodes,0,sizeof nodes); evals=0; found=0; clock_t t0=clock();
    dfs(&sf,r,0,-1); uint64_t tot=0; for(int i=0;i<32;i++) tot+=nodes[i];
    printf("bound %d: nodes %llu evals %llu found %d time %.1fs  per-depth:",B,(unsigned long long)tot,(unsigned long long)evals,found,(double)(clock()-t0)/CLOCKS_PER_SEC);
    for(int i=0;i<=B;i++) printf(" %llu",(unsigned long long)nodes[i]); printf("\n"); fflush(stdout);}
}
