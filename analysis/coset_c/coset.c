// Rokicki-style coset solver (reference implementation, untrusted) for the cells of Kociemba phase 1.
// A cell is a right coset Hg, H = <U,D,R2,L2,F2,B2>. For the coset of a = eval(wa) we index x in Ha by
// u = a * x^-1 in H (19,508,428,800 elements) and compute f_d = { x in Ha : x has a word of length <= d }:
//   f_d = f_{d-1} ∪ f_{d-1}·A ∪ { a*eval(v) : |v| = d, a*eval(v) in H, v canonical, last move not in A }
// (bit u set <=> x_u solvable within d; bit u*m for m in A <=> x' = m^-1 x_u, solvable within d+1).
// Model and move/cell conventions are those of the Lean development (Cube/Model.lean, k1dist.bin).
// Usage: coset D S "w a w o r d" [threads]   (D = max depth, S = max search length; word in move codes 0..17)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <omp.h>

// ---------------- cube model (as Lean) ----------------
typedef struct { uint8_t cp[8], co[8], ep[12], eo[12]; } St;
static const St basic[6] = {
  {{3,0,1,2,4,5,6,7},{0,0,0,0,0,0,0,0},{3,0,1,2,4,5,6,7,8,9,10,11},{0,0,0,0,0,0,0,0,0,0,0,0}}, // U
  {{4,1,2,0,7,5,6,3},{2,0,0,1,1,0,0,2},{8,1,2,3,11,5,6,7,4,9,10,0},{0,0,0,0,0,0,0,0,0,0,0,0}}, // R
  {{1,5,2,3,0,4,6,7},{1,2,0,0,2,1,0,0},{0,9,2,3,4,8,6,7,1,5,10,11},{0,1,0,0,0,1,0,0,1,1,0,0}}, // F
  {{0,1,2,3,5,6,7,4},{0,0,0,0,0,0,0,0},{0,1,2,3,5,6,7,4,8,9,10,11},{0,0,0,0,0,0,0,0,0,0,0,0}}, // D
  {{0,2,6,3,4,1,5,7},{0,1,2,0,0,2,1,0},{0,1,10,3,4,5,9,7,8,2,6,11},{0,0,0,0,0,0,0,0,0,0,0,0}}, // L
  {{0,1,3,7,4,5,2,6},{0,0,1,2,0,0,2,1},{0,1,2,11,4,5,6,10,8,9,3,7},{0,0,0,1,0,0,0,1,0,0,1,1}}};// B
static St smul(const St *s, const St *m) {
  St r;
  for (int i = 0; i < 8; i++) { r.cp[i] = s->cp[m->cp[i]]; r.co[i] = (s->co[m->cp[i]] + m->co[i]) % 3; }
  for (int i = 0; i < 12; i++) { r.ep[i] = s->ep[m->ep[i]]; r.eo[i] = (s->eo[m->ep[i]] + m->eo[i]) % 2; }
  return r;
}
static St MV[18];
static St sid(void) { St r; for (int i = 0; i < 8; i++) { r.cp[i] = i; r.co[i] = 0; } for (int i = 0; i < 12; i++) { r.ep[i] = i; r.eo[i] = 0; } return r; }

// ---------------- permutation coordinates ----------------
static int lehmer(const uint8_t *p, int n) { int r = 0; for (int i = 0; i < n; i++) { int c = 0; for (int j = i + 1; j < n; j++) if (p[j] < p[i]) c++; r = r * (n - i) + c; } return r; }
static int lpar(const uint8_t *p, int n) { int s = 0; for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (p[j] < p[i]) s++; return s & 1; }
static uint8_t P8[40320][8], P4[24][4];
static uint8_t par8[40320], par4[24], sRank[24], sOf[2][12];
static int32_t (*cMove)[10], (*eMove)[10]; static int8_t sMove[24][10];
static const int AM[10] = {0, 1, 2, 9, 10, 11, 4, 13, 7, 16}; // U U2 U' D D2 D' R2 L2 F2 B2
static int isA[18];
static uint16_t FT[10][2][4096];
static int nextperm(uint8_t *a, int n) { int i = n - 2; while (i >= 0 && a[i] >= a[i + 1]) i--; if (i < 0) return 0;
  int j = n - 1; while (a[j] <= a[i]) j--; uint8_t t = a[i]; a[i] = a[j]; a[j] = t;
  for (int l = i + 1, r = n - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; } return 1; }
static void build_tables(void) {
  uint8_t a[8] = {0,1,2,3,4,5,6,7}; int k = 0;
  do { memcpy(P8[k], a, 8); if (lehmer(a, 8) != k) { fprintf(stderr, "lehmer8\n"); exit(1); } par8[k] = lpar(a, 8); k++; } while (nextperm(a, 8));
  uint8_t b[4] = {0,1,2,3}; k = 0; int cnt[2] = {0, 0};
  do { memcpy(P4[k], b, 4); par4[k] = lpar(b, 4); sRank[k] = cnt[par4[k]]; sOf[par4[k]][cnt[par4[k]]++] = k; k++; } while (nextperm(b, 4));
  cMove = malloc(sizeof(int32_t[10]) * 40320); eMove = malloc(sizeof(int32_t[10]) * 40320);
  for (int t = 0; t < 10; t++) {
    const St *m = &MV[AM[t]];
    for (int i = 0; i < 40320; i++) {
      uint8_t q[8];
      for (int j = 0; j < 8; j++) q[j] = P8[i][m->cp[j]];
      cMove[i][t] = lehmer(q, 8);
      for (int j = 0; j < 8; j++) { if (m->ep[j] >= 8) { fprintf(stderr, "A move leaves UD\n"); exit(1); } q[j] = P8[i][m->ep[j]]; }
      eMove[i][t] = lehmer(q, 8);
    }
    for (int s = 0; s < 24; s++) { uint8_t q[4]; for (int j = 0; j < 4; j++) q[j] = P4[s][m->ep[8 + j] - 8]; sMove[s][t] = lehmer(q, 4); }
    for (int p = 0; p < 2; p++) for (int v = 0; v < 4096; v++) {
      uint16_t w = 0; for (int j = 0; j < 12; j++) if (v >> j & 1) { int s2 = sMove[sOf[p][j]][t]; w |= 1 << sRank[s2]; }
      FT[t][p][v] = w;
    }
  }
}

// ---------------- bitmap over H ----------------
#define NB 40320L
#define BLK 60480L  // 40320 fields of 12 bits
#define HSIZE 19508428800L
static inline unsigned getf(const uint8_t *blk, long e) { long o = (3 * e) >> 1; unsigned w = blk[o] | (blk[o + 1] << 8); return (e & 1) ? (w >> 4) : (w & 0xFFF); }
static inline void orf(uint8_t *blk, long e, unsigned v) { long o = (3 * e) >> 1; if (e & 1) { blk[o] |= (v << 4) & 0xF0; blk[o + 1] |= v >> 4; } else { blk[o] |= v & 0xFF; blk[o + 1] |= (v >> 8) & 0x0F; } }
static uint8_t *alloc_bm(void) { uint8_t *p = mmap(0, NB * BLK, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0); if (p == MAP_FAILED) { perror("bitmap"); exit(1); } return p; }
static void free_bm(uint8_t *p) { munmap(p, NB * BLK); }
static long hindex_bit(const uint8_t *c, const uint8_t *e, long *blk, long *fe, int *bit) {
  uint8_t s[4]; for (int i = 0; i < 4; i++) s[i] = e[8 + i] - 8;
  int ci = lehmer(c, 8), ei = lehmer(e, 8), si = lehmer(s, 4);
  if ((par8[ci] ^ par8[ei]) != par4[si]) { fprintf(stderr, "parity violation\n"); exit(1); }
  *blk = ci; *fe = ei; *bit = sRank[si]; return 0;
}
static long popcnt_bm(const uint8_t *bm) { long n = 0; const uint64_t *q = (const uint64_t *)bm; long nw = NB * BLK / 8; for (long i = 0; i < nw; i++) n += __builtin_popcountll(q[i]); return n; }

// prepass: NEW = OLD ∪ OLD·A
static uint8_t *prepass(uint8_t *old) {
  uint8_t *nw = alloc_bm();
  memcpy(nw, old, NB * BLK);
  for (int t = 0; t < 10; t++) {
    #pragma omp parallel for schedule(dynamic, 64)
    for (long c = 0; c < NB; c++) {
      const uint8_t *src = old + c * BLK; uint8_t *dst = nw + (long)cMove[c][t] * BLK; int pc = par8[c];
      for (long e = 0; e < 40320; e++) {
        unsigned v = getf(src, e); if (!v) continue;
        orf(dst, eMove[e][t], FT[t][pc ^ par8[e]][v]);
      }
    }
  }
  free_bm(old);
  return nw;
}

// ---------------- phase-1 cells (Lean coding) ----------------
static int32_t *TE, *TC, *TS; static uint8_t *d1; static long idCell;
static void *loadf(const char *f) { FILE *fp = fopen(f, "rb"); if (!fp) { perror(f); exit(1); } fseek(fp, 0, SEEK_END); size_t sz = ftell(fp); fseek(fp, 0, SEEK_SET);
  void *p = malloc(sz); if (fread(p, 1, sz, fp) != sz) { perror("read"); exit(1); } fclose(fp); return p; }
static inline long nxt(long i, int m) { long e = i / (2187L * 495), c = (i / 495) % 2187, s = i % 495;
  return ((long)TE[e * 18 + m] * 2187 + TC[c * 18 + m]) * 495 + TS[s * 18 + m]; }

// ---------------- search ----------------
static uint8_t *BM; static long nsol, nnode;
static void dfs(int r, long cell, const uint8_t *c, const uint8_t *e, int lf, int lastA) {
  nnode++;
  if (r == 0) {
    if (cell == idCell && !lastA) { long b, fe; int bit; hindex_bit(c, e, &b, &fe, &bit); orf(BM + b * BLK, fe, 1u << bit); nsol++; }
    return;
  }
  for (int m = 0; m < 18; m++) {
    int f = m / 3;
    if (f == lf) continue;
    if (lf < 6 && f % 3 == lf % 3 && f < lf) continue;
    if (r == 1 && isA[m]) continue;
    long c2 = nxt(cell, m);
    if (d1[c2] > r - 1) continue;
    uint8_t cc[8], ee[12];
    for (int i = 0; i < 8; i++) cc[i] = c[MV[m].cp[i]];
    for (int i = 0; i < 12; i++) ee[i] = e[MV[m].ep[i]];
    dfs(r - 1, c2, cc, ee, f, isA[m]);
  }
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: coset D S \"word\" [threads]\n"); return 1; }
  int D = atoi(argv[1]), S = atoi(argv[2]);
  if (argc > 4) omp_set_num_threads(atoi(argv[4]));
  for (int f = 0; f < 6; f++) { St b = basic[f], b2 = smul(&b, &b), b3 = smul(&b2, &b); MV[3 * f] = b; MV[3 * f + 1] = b2; MV[3 * f + 2] = b3; }
  for (int t = 0; t < 10; t++) isA[AM[t]] = 1;
  build_tables();
  TE = loadf("/root/f28/TE.bin"); TC = loadf("/root/f28/TC.bin"); TS = loadf("/root/f28/TS.bin");
  { FILE *fi = fopen("/root/f28/I0.txt", "r"); if (fscanf(fi, "%ld", &idCell) != 1) return 2; fclose(fi); }
  { int fd = open("/root/inter/k1dist.bin", O_RDONLY); struct stat st; fstat(fd, &st);
    d1 = mmap(0, st.st_size, PROT_READ, MAP_SHARED, fd, 0); if (d1 == MAP_FAILED) { perror("mmap"); return 3; } }
  // representative a = eval(word)
  St a = sid(); long cell = idCell; int wl = 0;
  { char *s = argv[3]; char *tok = strtok(s, " "); while (tok) { int m = atoi(tok); a = smul(&a, &MV[m]); cell = nxt(cell, m); wl++; tok = strtok(0, " "); } }
  printf("coset word length %d, cell %ld, d1 %d\n", wl, cell, d1[cell]); fflush(stdout);
  BM = alloc_bm();
  time_t t0 = time(0);
  for (int d = 0; d <= D; d++) {
    if (d > 0) { madvise(d1, 2217093120L, MADV_DONTNEED); BM = prepass(BM); }
    long ns0 = nsol, nn0 = nnode;
    if (d <= S) { madvise(d1, 2217093120L, MADV_WILLNEED); dfs(d, cell, a.cp, a.ep, 6, 0); }
    long cnt = popcnt_bm(BM);
    printf("depth %2d  covered %12ld / %ld  search sols %ld nodes %ld  t=%lds\n", d, cnt, HSIZE, nsol - ns0, nnode - nn0, (long)(time(0) - t0));
    fflush(stdout);
    if (cnt == HSIZE) { printf("COSET BOUND %d\n", d); return 0; }
  }
  printf("NOT COVERED at %d\n", D);
  return 0;
}
