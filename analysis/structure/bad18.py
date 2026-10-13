import json,re,sys; sys.path.insert(0,'/root/explore')
from collections import Counter
from cubie import cycles
SY=[(tuple(a),tuple(b)) for a,b in json.load(open('/root/kph2/syms.json'))['syms']]
B=[]
for l in open('/root/f28/bad18.txt'):
    m=re.findall(r'#\[([0-9,]*)\]',l)
    if m: B.append((tuple(map(int,m[0].split(','))),tuple(map(int,m[1].split(',')))))
B=set(B); print('Bad18 size',len(B))
def pm(a,b): return tuple(a[b[i]] for i in range(len(b)))
def pinv(a):
    r=[0]*len(a)
    for i,x in enumerate(a): r[x]=i
    return tuple(r)
def mul(g,h): return (pm(g[0],h[0]),pm(g[1],h[1]))
def inv(g): return (pinv(g[0]),pinv(g[1]))
def conj(s,g): return mul(mul(s,g),inv(s))
print('closed under conj:',all(conj(s,g) in B for s in SY for g in B),' under inverse:',all(inv(g) in B for g in B))
seen=set(); orbits=[]
for g in sorted(B):
    if g in seen: continue
    o={conj(s,x) for s in SY for x in (g,inv(g))}; seen|=o; orbits.append(sorted(o))
print('orbits under 16 syms + inversion:',len(orbits),Counter(len(o) for o in orbits))
def ctype(p): return tuple(sorted((len(c) for c in cycles(p)),reverse=True))
from math import lcm
def order(g): 
    o=1
    for p in g:
        for c in cycles(p): o=lcm(o,len(c))
    return o
print('corner cycle types',Counter(ctype(g[0]) for g in B))
print('U/D edge cycle types',Counter(ctype(g[1][:8]) for g in B))
print('E-slice cycle types',Counter(ctype(tuple(x-8 for x in g[1][8:])) for g in B))
print('orders',Counter(order(g) for g in B))
# which U/D edges change layer
def layerswap(g): return sum(1 for i in range(8) if (g[1][i]<4)!=(i<4))
print('U/D edges changing layer (U<->D)',Counter(layerswap(g) for g in B))
def cornlayer(g): return sum(1 for i in range(8) if (g[0][i]<4)!=(i<4))
print('corners changing layer',Counter(cornlayer(g) for g in B))
print('corners solved',sum(1 for g in B if g[0]==tuple(range(8))))
for o in orbits: 
    g=o[0]; print(len(o),'cp',g[0],'ep',g[1],'ord',order(g))
print('-----cores')
core=Counter((g[0],g[1][:8]) for g in B)
print('distinct cores (cp, U/D edges):',len(core),' E-perms per core:',Counter(core.values()))
def par(p): return sum(1 for i in range(len(p)) for j in range(i) if p[j]>p[i])%2
cores=sorted(core)
# orbits of cores under syms+inv: act on full elements then project
corb=set(); co_orbits=[]
for c in cores:
    if c in corb: continue
    g=[x for x in B if (x[0],x[1][:8])==c][0]
    o={ (y[0],y[1][:8]) for s in SY for x in (g,inv(g)) for y in [conj(s,x)]}
    corb|=o; co_orbits.append((c,len(o)))
print('core orbits:',len(co_orbits))
for c,n in co_orbits:
    Es=sorted(tuple(x-8 for x in g[1][8:]) for g in B if (g[0],g[1][:8])==c)
    print(n,'cp',c[0],'UD',c[1],'Epar',par(Es[0]),'#E',len(Es),'ctype',ctype(c[0]),ctype(c[1]))
