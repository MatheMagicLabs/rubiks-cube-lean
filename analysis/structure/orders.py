# Exact order statistics of the Rubik's cube group by cycle type (no enumeration of elements)
from math import factorial, gcd, prod
from itertools import product
from collections import Counter
def lcm(a,b): return a*b//gcd(a,b)
def partitions(n,m=None):
    if m is None: m=n
    if n==0: yield []; return
    for k in range(min(n,m),0,-1):
        for p in partitions(n-k,k): yield [k]+p
def nperm(part,n):
    c=Counter(part); return factorial(n)//prod(L**m*factorial(m) for L,m in c.items())
def side(n,q):  # q = orientation modulus; returns {parity: Counter(order -> count)}
    res={0:Counter(),1:Counter()}
    for part in partitions(n):
        par=(n-len(part))%2; np_=nperm(part,n)
        for ts in product(range(q),repeat=len(part)):
            if sum(ts)%q: continue
            # each cycle of length L with prescribed sum: q^(L-1) assignments
            cnt=np_*prod(q**(L-1) for L in part)
            o=1
            for L,t in zip(part,ts): o=lcm(o, L if t==0 else q*L)
            res[par][o]+=cnt
    return res
C=side(8,3); E=side(12,2)
G=Counter()
for par in (0,1):
    for oc,nc in C[par].items():
        for oe,ne in E[par].items(): G[lcm(oc,oe)]+=nc*ne
N=sum(G.values())
print('|G| =',N, N==43252003274489856000)
print('number of distinct orders:',len(G),' max order:',max(G))
for o in sorted(G): print(o,G[o])
# Frobenius check: #{x: x^n=1} divisible by n for each n dividing |G| among small n
bad=[n for n in range(1,1300) if N%n==0 and sum(c for o,c in G.items() if n%o==0)%n]
print('Frobenius violations:',bad)
import json; json.dump({str(k):v for k,v in G.items()},open('order_dist.json','w'))
