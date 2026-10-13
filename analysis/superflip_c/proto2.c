// Feasibility check for a 28-move bound: Kociemba phase 1 + phase 2 with coset-difference arguments.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#define NE 967680
#define NC 2768
static uint8_t *d1, *d2;
static int32_t *TE, *TC, *TS, *clsT, *syT, *repsT, *stabOff, *stabFlat, *epCj, *cpLean, *epLean;
static uint8_t *cpGL, *epGL, *symC, *symCi, *symE, *symEi, *MC, *ME;
static long I0;

static void *loadf(const char *f, size_t *n) {
  FILE *fp = fopen(f, "rb"); if (!fp) { perror(f); exit(1); }
  fseek(fp, 0, SEEK_END); size_t sz = ftell(fp); fseek(fp, 0, SEEK_SET);
  void *p = malloc(sz); if (fread(p, 1, sz, fp) != sz) { perror("read"); exit(1); } fclose(fp);
  if (n) *n = sz; return p;
}
static uint8_t *mapf(const char *f) {
  int fd = open(f, O_RDONLY); struct stat st; fstat(fd, &st);
  void *p = mmap(0, st.st_size, PROT_READ, MAP_SHARED, fd, 0); if (p == MAP_FAILED) { perror("mmap"); exit(1); }
  return p;
}
// ---- permutations: elements as (cp[8], ep[12]); product (x*y)[i] = x[y[i]] ----
typedef struct { uint8_t c[8], e[12]; } P;
static void pmul(const P *x, const P *y, P *z) { for (int i = 0; i < 8; i++) z->c[i] = x->c[y->c[i]]; for (int i = 0; i < 12; i++) z->e[i] = x->e[y->e[i]]; }
static void pinv(const P *x, P *z) { for (int i = 0; i < 8; i++) z->c[x->c[i]] = i; for (int i = 0; i < 12; i++) z->e[x->e[i]] = i; }
static int lehmer(const uint8_t *p, int n) { int r = 0; for (int i = 0; i < n; i++) { int c = 0; for (int j = i + 1; j < n; j++) if (p[j] < p[i]) c++; r = r * (n - i) + c; } return r; }
static uint64_t enc(const P *x) { // H elements only
  uint8_t es[4]; for (int i = 0; i < 4; i++) es[i] = x->e[8 + i] - 8;
  return (uint64_t)lehmer(x->c, 8) * NE + (uint64_t)lehmer(x->e, 8) * 24 + lehmer(es, 4);
}
static int inH(const P *x) { for (int i = 0; i < 8; i++) if (x->e[i] >= 8) return 0; return 1; }
static void conjP(int s, const P *x, P *z) { // conj_s(p)[i] = sinv[p[s[i]]]
  for (int i = 0; i < 8; i++) z->c[i] = symCi[s * 8 + x->c[symC[s * 8 + i]]];
  for (int i = 0; i < 12; i++) z->e[i] = symEi[s * 12 + x->e[symE[s * 12 + i]]];
}
static long cellOf(const P *x) {
  int r = cpLean[lehmer(x->c, 8)]; int c = clsT[r], s = syT[r];
  uint8_t q[12]; for (int i = 0; i < 12; i++) q[i] = symEi[s * 12 + x->e[symE[s * 12 + i]]];
  uint8_t es[4]; for (int i = 0; i < 4; i++) es[i] = q[8 + i] - 8;
  int e0 = epLean[lehmer(q, 8) * 24 + lehmer(es, 4)], e = e0;
  for (int k = stabOff[c]; k < stabOff[c + 1]; k++) { int v = epCj[(long)e0 * 16 + stabFlat[k]]; if (v < e) e = v; }
  return (long)c * NE + e;
}
static int dH(const P *x) { return d2[cellOf(x)]; }
// ---- phase 1 ----
static inline long nxt(long i, int m) {
  long e = i / (2187L * 495), c = (i / 495) % 2187, s = i % 495;
  return ((long)TE[e * 18 + m] * 2187 + TC[c * 18 + m]) * 495 + TS[s * 18 + m];
}
#define MAXS 64

static int nsol, solw[MAXS][16], sollen[MAXS], wbuf[16];
// all canonical words of length exactly L from cell i to I0 (up to cap)
static void dfs(long i, int depth, int L, int last, int cap) {
  if (nsol >= cap) return;
  if (depth == L) { if (i == I0) { memcpy(solw[nsol], wbuf, sizeof(int) * L); sollen[nsol] = L; nsol++; } return; }
  int rem = L - depth;
  for (int m = 0; m < 18; m++) {
    int f = m / 3;
    if (last >= 0 && (f == last || (f % 3 == last % 3 && f < last))) continue;
    long j = nxt(i, m);
    if (d1[j] > rem - 1) continue;
    wbuf[depth] = m; dfs(j, depth + 1, L, f, cap);
    if (nsol >= cap) return;
  }
}
static void evalw(const int *w, int n, P *x) { P a, t; for (int i = 0; i < 8; i++) a.c[i] = i; for (int i = 0; i < 12; i++) a.e[i] = i;
  for (int k = 0; k < n; k++) { P m; memcpy(m.c, MC + w[k] * 8, 8); memcpy(m.e, ME + w[k] * 12, 12); pmul(&a, &m, &t); a = t; } *x = a; }
// ---- bad sets ----
static int cmpu(const void *a, const void *b) { uint64_t x = *(uint64_t *)a, y = *(uint64_t *)b; return x < y ? -1 : x > y; }
static P *bad18, *bad17; static long nb18, nb17;
static uint64_t *kbad; static long nkbad;
static int inK(uint64_t k) { long lo = 0, hi = nkbad - 1; while (lo <= hi) { long mid = (lo + hi) / 2; if (kbad[mid] == k) return 1; if (kbad[mid] < k) lo = mid + 1; else hi = mid - 1; } return 0; }
static void buildBad(int minD, P **out, long *nout) {
  long cap = 1 << 20, n = 0; P *L = malloc(sizeof(P) * cap);
  for (long cell = 0; cell < (long)NC * NE; cell++) {
    if (d2[cell] < minD || d2[cell] == 255) continue;
    int c = cell / NE, e = cell % NE; P st; memcpy(st.c, cpGL + (long)repsT[c] * 8, 8); memcpy(st.e, epGL + (long)e * 12, 12);
    for (int s = 0; s < 16; s++) { if (n == cap) { cap *= 2; L = realloc(L, sizeof(P) * cap); } conjP(s, &st, &L[n++]); }
  }
  // dedupe by encoding
  uint64_t *k = malloc(8 * n); for (long i = 0; i < n; i++) k[i] = enc(&L[i]) * 0 + (uint64_t)i; // placeholder index sort below
  // sort indices by enc
  uint64_t *ek = malloc(16 * n);
  for (long i = 0; i < n; i++) { ek[2 * i] = enc(&L[i]); ek[2 * i + 1] = i; }
  qsort(ek, n, 16, cmpu);
  long m = 0; P *U = malloc(sizeof(P) * n);
  for (long i = 0; i < n; i++) { if (i > 0 && ek[2 * i] == ek[2 * (i - 1)]) continue; U[m++] = L[ek[2 * i + 1]]; }
  // verify each really has distance >= minD
  long badcnt = 0; for (long i = 0; i < m; i++) if (dH(&U[i]) < minD) badcnt++;
  fprintf(stderr, "bad set d>=%d: %ld elements (%ld raw), %ld inconsistent\n", minD, m, n, badcnt);
  free(L); free(k); free(ek); *out = U; *nout = m;
}

// ===== superflip stage-1 search with run normalisation =====
static int HUD[18], isH[3][18], mu3[3][18];
static uint64_t cnt_nodes[32], cnt_leaves, cnt_evals; static int BOUND=19, firstSet=1; static long bad=0;
static int minSlack=99; static int ORDER=1;
static void sdfs(const long *r, const P *perm, int g, int lastf, const int *run, int maxRun, int lastNonH){
  cnt_nodes[g]++;
  if (g>0 && d1[r[0]]==0 && lastNonH){ // s1 can end here: sf.s1 in H
    cnt_leaves++;
    int dh=dH(perm); int need = dh>maxRun?dh:maxRun;
    int slack = g+need-20; if(slack<minSlack) minSlack=slack;
    if (g+need<=19){ bad++; if(bad<5){fprintf(stderr,"COUNTEREXAMPLE? g=%d dh=%d maxRun=%d\n",g,dh,maxRun);} }
  }
  for(int f=0;f<6;f++){ if(lastf>=0 && (f==lastf || (ORDER && f%3==lastf%3 && f<lastf))) continue;
    for(int k=0;k<3;k++){ int m=3*f+k;
      if(g==0){ if(firstSet==1 && m!=3) continue; if(firstSet==2 && !(m==3||m==5)) continue; if(firstSet==3 && HUD[m]) continue; }
      long rr[3]; rr[0]=nxt(r[0],m); rr[1]=nxt(r[1],mu3[1][m]); rr[2]=nxt(r[2],mu3[2][m]);
      int nrun[3], mr=maxRun; for(int a=0;a<3;a++){ nrun[a]= isH[a][m]? run[a]+1:0; if(nrun[a]>mr) mr=nrun[a]; }
      cnt_evals++;
      int g1=g+1;
      if (g1 + d1[rr[0]] + mr > BOUND) continue;
      if (g1 + d1[rr[1]] > BOUND || g1 + d1[rr[2]] > BOUND) continue;
      P np; P mv; memcpy(mv.c, MC+m*8, 8); memcpy(mv.e, ME+m*12, 12); pmul(perm,&mv,&np);
      sdfs(rr,&np,g1,f,nrun,mr,!HUD[m]);
    }}
}
int main(int argc,char**argv){
  BOUND=atoi(argv[1]); firstSet=atoi(argv[2]); ORDER=atoi(argv[3]);
  d1 = mapf("/root/inter/k1dist.bin"); d2 = mapf("/root/inter/k2dist.bin");
  TE = loadf("TE.bin", 0); TC = loadf("TC.bin", 0); TS = loadf("TS.bin", 0); clsT = loadf("clsT.bin", 0); syT = loadf("syT.bin", 0);
  repsT = loadf("repsT.bin", 0); stabOff = loadf("stabOff.bin", 0); stabFlat = loadf("stabFlat.bin", 0); epCj = loadf("epCj.bin", 0);
  cpLean = loadf("cpLean.bin", 0); epLean = loadf("epLean.bin", 0); cpGL = loadf("cpGL.bin", 0); epGL = loadf("epGL.bin", 0);
  symC = loadf("symC.bin", 0); symCi = loadf("symCi.bin", 0); symE = loadf("symE.bin", 0); symEi = loadf("symEi.bin", 0);
  MC = loadf("MC.bin", 0); ME = loadf("ME.bin", 0);
  FILE *fi = fopen("I0.txt", "r"); if(fscanf(fi, "%ld", &I0)!=1) return 1; fclose(fi);
  int hl[10]={0,1,2,9,10,11,4,13,7,16}; memset(HUD,0,sizeof HUD); for(int i=0;i<10;i++) HUD[hl[i]]=1;
  int MU[18]={6,7,8,0,1,2,3,4,5,15,16,17,9,10,11,12,13,14}; // S m S^-1: U->F, R->U, F->R, D->B, L->D, B->L
  for(int m=0;m<18;m++){ mu3[0][m]=m; mu3[1][m]=MU[m]; mu3[2][m]=MU[MU[m]]; }
  for(int a=0;a<3;a++) for(int m=0;m<18;m++) isH[a][m]=HUD[mu3[a][m]];
  // superflip phase-1 rank: eo all 1, co 0, slice solved. compute via the Lean listings
  FILE *f=fopen("/root/inter/eoL.txt","r"); int eidx=-1; for(int k=0;k<2048;k++){int ok=1;for(int i=0;i<12;i++){int v;if(fscanf(f,"%d",&v)!=1)return 2; if(v!=1) ok=0;} if(ok) eidx=k;} fclose(f);
  long i0e = I0/(2187L*495); long rsf = I0 - i0e*2187L*495 + (long)eidx*2187L*495;
  fprintf(stderr,"sf rank %ld d1 %d\n", rsf, d1[rsf]);
  long r[3]={rsf,rsf,rsf}; P id; for(int i=0;i<8;i++) id.c[i]=i; for(int i=0;i<12;i++) id.e[i]=i;
  int run[3]={0,0,0};
  sdfs(r,&id,0,-1,run,0,0);
  uint64_t tot=0; for(int i=0;i<32;i++) tot+=cnt_nodes[i];
  printf("bound %d first %d: nodes %llu evals %llu leaves %llu bad %ld minSlack %d\nper depth:",BOUND,firstSet,(unsigned long long)tot,(unsigned long long)cnt_evals,(unsigned long long)cnt_leaves,bad,minSlack);
  for(int i=0;i<=BOUND;i++) printf(" %llu",(unsigned long long)cnt_nodes[i]); printf("\n");
}
