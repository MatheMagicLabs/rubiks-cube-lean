// V1: independent count of H elements reachable by words of length <= L (coset H, a = id), by brute enumeration.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef struct { uint8_t cp[8], co[8], ep[12], eo[12]; } St;
static const St basic[6] = {
  {{3,0,1,2,4,5,6,7},{0,0,0,0,0,0,0,0},{3,0,1,2,4,5,6,7,8,9,10,11},{0,0,0,0,0,0,0,0,0,0,0,0}},
  {{4,1,2,0,7,5,6,3},{2,0,0,1,1,0,0,2},{8,1,2,3,11,5,6,7,4,9,10,0},{0,0,0,0,0,0,0,0,0,0,0,0}},
  {{1,5,2,3,0,4,6,7},{1,2,0,0,2,1,0,0},{0,9,2,3,4,8,6,7,1,5,10,11},{0,1,0,0,0,1,0,0,1,1,0,0}},
  {{0,1,2,3,5,6,7,4},{0,0,0,0,0,0,0,0},{0,1,2,3,5,6,7,4,8,9,10,11},{0,0,0,0,0,0,0,0,0,0,0,0}},
  {{0,2,6,3,4,1,5,7},{0,1,2,0,0,2,1,0},{0,1,10,3,4,5,9,7,8,2,6,11},{0,0,0,0,0,0,0,0,0,0,0,0}},
  {{0,1,3,7,4,5,2,6},{0,0,1,2,0,0,2,1},{0,1,2,11,4,5,6,10,8,9,3,7},{0,0,0,1,0,0,0,1,0,0,1,1}}};
static St smul(const St *s, const St *m) { St r;
  for (int i = 0; i < 8; i++) { r.cp[i] = s->cp[m->cp[i]]; r.co[i] = (s->co[m->cp[i]] + m->co[i]) % 3; }
  for (int i = 0; i < 12; i++) { r.ep[i] = s->ep[m->ep[i]]; r.eo[i] = (s->eo[m->ep[i]] + m->eo[i]) % 2; } return r; }
static St MV[18];
static int lehmer(const uint8_t *p, int n) { int r = 0; for (int i = 0; i < n; i++) { int c = 0; for (int j = i + 1; j < n; j++) if (p[j] < p[i]) c++; r = r * (n - i) + c; } return r; }
static uint64_t *buf; static long nb, cap; static int L;
static void rec(const St *x, int len, int lf) {
  int inH = 1; for (int i = 0; i < 8; i++) if (x->co[i]) inH = 0; for (int i = 0; i < 12; i++) if (x->eo[i]) inH = 0;
  for (int i = 0; i < 8 && inH; i++) if (x->ep[i] >= 8) inH = 0;
  if (inH) { uint8_t s[4]; for (int i = 0; i < 4; i++) s[i] = x->ep[8 + i] - 8;
    uint64_t key = ((uint64_t)lehmer(x->cp, 8) * 40320 + lehmer(x->ep, 8)) * 24 + lehmer(s, 4);
    if (nb == cap) { cap = cap ? 2 * cap : 1 << 20; buf = realloc(buf, cap * 8); }
    buf[nb++] = key * 32 + len; }
  if (len == L) return;
  for (int m = 0; m < 18; m++) { int f = m / 3; if (f == lf) continue; if (lf < 6 && f % 3 == lf % 3 && f < lf) continue;
    St y = smul(x, &MV[m]); rec(&y, len + 1, f); }
}
static int cmp(const void *a, const void *b) { uint64_t x = *(uint64_t *)a, y = *(uint64_t *)b; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
  L = atoi(argv[1]);
  for (int f = 0; f < 6; f++) { St b = basic[f], b2 = smul(&b, &b), b3 = smul(&b2, &b); MV[3*f] = b; MV[3*f+1] = b2; MV[3*f+2] = b3; }
  St id; for (int i = 0; i < 8; i++) { id.cp[i] = i; id.co[i] = 0; } for (int i = 0; i < 12; i++) { id.ep[i] = i; id.eo[i] = 0; }
  rec(&id, 0, 6);
  qsort(buf, nb, 8, cmp);   // sorted by key then len: first occurrence = min length
  long cnt[32] = {0}; uint64_t prev = ~0ULL;
  for (long i = 0; i < nb; i++) { uint64_t k = buf[i] / 32; if (k != prev) { cnt[buf[i] % 32]++; prev = k; } }
  long cum = 0; for (int d = 0; d <= L; d++) { cum += cnt[d]; printf("depth %2d  new %10ld  covered %12ld\n", d, cnt[d], cum); }
  return 0;
}
