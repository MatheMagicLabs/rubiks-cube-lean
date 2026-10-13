# Closure of the found 20-move superflip words under cyclic shifts, the 48 symmetries, inversion and
# commuting swaps; count all minimal solutions; check that every closure word satisfying the search's
# acceptance conditions was found (completeness check within the found orbits).
import itertools, sys
import numpy as np
from sc_check import apply_word, solved, is_superflip, mats, N, NI, FACES
found=[]
for fn in sys.argv[1:]:
    for line in open(fn):
        if '|' in line: found.append(tuple(int(x) for x in line.split('|')[0].split()))
found=set(found)
symmaps=[]
for A in mats:
    d=int(round(np.linalg.det(A)))
    fm=[FACES.index(NI[tuple(int(x) for x in A@np.array(N[f]))]) for f in FACES]
    mm=[]
    for m in range(18):
        f,k=m//3,m%3
        k2=k if d>0 else (1 if k==1 else 2-k)
        mm.append(3*fm[f]+k2)
    symmaps.append(mm)
def inv(w): return tuple((3*(m//3)+(1 if m%3==1 else 2-m%3)) for m in reversed(w))
def swaps(w):
    # all words obtained by reordering adjacent opposite-face pairs (same axis, different faces)
    out={w}; frontier=[w]
    while frontier:
        x=frontier.pop(); 
        for i in range(len(x)-1):
            a,b=x[i]//3,x[i+1]//3
            if a!=b and a%3==b%3:
                y=x[:i]+(x[i+1],x[i])+x[i+2:]
                if y not in out: out.add(y); frontier.append(y)
    return out
clo=set(); frontier=list(found)
for w in found: clo.add(w)
while frontier:
    w=frontier.pop()
    nb=[w[i:]+w[:i] for i in range(1,len(w))]+[tuple(mm[m] for m in w) for mm in symmaps]+[inv(w)]
    nb+=list(swaps(w))
    for x in nb:
        if x not in clo: clo.add(x); frontier.append(x)
print("found normal-form words:",len(found))
print("all minimal solutions (closure, as move sequences):",len(clo))
canon=[w for w in clo if all(not(w[i]//3%3==w[i+1]//3%3 and w[i+1]//3<w[i]//3) for i in range(len(w)-1))]
print("of which canonical (opposite faces in fixed order):",len(canon))
# sanity: random sample evaluates to the superflip
import random
smp=random.sample(sorted(clo),min(300,len(clo)))
print("sticker check of 300 random closure words:",sum(is_superflip(apply_word(solved,list(w))) for w in smp),"/",len(smp))
# acceptance conditions of the search
HUD={0,1,2,9,10,11,4,13,7,16}
MU=[6,7,8,0,1,2,3,4,5,15,16,17,9,10,11,12,13,14]
mu=[list(range(18)),MU,[MU[MU[m]] for m in range(18)]]
def accepted(w):
    n=len(w)
    if w[0] not in (3,5): return False
    # canonical order within s1 and s2 (boundary free)
    t=0
    while t<n and w[n-1-t] in HUD: t+=1
    s1=w[:n-t]; s2=w[n-t:]
    if len(s1)==0 or w[n-t-1] in HUD: return False
    def canon_ok(x): return all(not(x[i]//3%3==x[i+1]//3%3 and x[i+1]//3<x[i]//3) for i in range(len(x)-1))
    if not canon_ok(s1) or not canon_ok(s2): return False
    if any(s1[i]//3==s1[i+1]//3 for i in range(len(s1)-1)): return False
    if s2 and s1[-1]//3==s2[0]//3: return False
    # runs inside s1 (all three axes) <= |s2|
    for a in range(3):
        r=0
        for m in s1:
            r = r+1 if mu[a][m] in HUD else 0
            if r>t: return False
    return True
acc=[w for w in clo if accepted(w)]
miss=[w for w in acc if w not in found]
extra=[w for w in found if w not in clo]
print("closure words satisfying the search's acceptance conditions:",len(acc),"; missing from search output:",len(miss))
for w in miss[:5]: print("  MISSING",w)
