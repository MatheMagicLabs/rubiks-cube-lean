import sys,re,json; sys.path.insert(0,'/root/explore')
from cubie import *
from collections import Counter
HM=[0,1,2,9,10,11,4,7,13,16,5,14]  # U,U2,U',D,D2,D',R2,F2? -> compute properly below
HM=[0,1,2, 9,10,11, 4, 7, 13, 16]   # U U2 U' D D2 D' R2 F2 L2 B2  (faces U0 R1 F2 D3 L4 B5)
assert [MNAME[m] for m in HM]==['U','U2',"U'",'D','D2',"D'",'R2','F2','L2','B2']
def bfs_proj(proj):
    start=proj(ID); dist={start:0}; fr=[ID]; d=0
    reps={start:ID}
    while fr:
        nf=[]
        for x in fr:
            for m in HM:
                y=mul(x,MOVES[m]); k=proj(y)
                if k not in dist: dist[k]=d+1; nf.append(y)
        fr=nf; d+=1
    return dist
dc=bfs_proj(lambda s:s[0]); du=bfs_proj(lambda s:s[2][:8]); de=bfs_proj(lambda s:s[2][8:])
dcu={}
for n,d in [('corners',dc),('UD edges',du),('E edges',de)]:
    h=Counter(d.values()); print(n,len(d),'max',max(h),[h[i] for i in range(max(h)+1)])
B=[]
for l in open('/root/f28/bad18.txt'):
    m=re.findall(r'#\[([0-9,]*)\]',l)
    if m: B.append((tuple(map(int,m[0].split(','))),tuple(map(int,m[1].split(',')))))
cores=sorted(set((g[0],g[1][:8]) for g in B))
print('cores',len(cores))
print('Bad18 cores: (corner dist, UD dist):',Counter((dc[c],du[u]) for c,u in cores))
# for comparison: distribution of (dc,du) max over all
print('Bad18: dC+dUD+dE histogram',Counter(dc[g[0]]+du[g[1][:8]]+de[g[1][8:]] for g in B))
print('Bad18: max(dC,dUD,dE) histogram',Counter(max(dc[g[0]],du[g[1][:8]],de[g[1][8:]]) for g in B))
m=((1,0,3,2,5,4,7,6),(2,1,0,3,6,5,4,7,9,8,11,10))
print('mirror element in Bad18:',m in set(B), 'components',dc[m[0]],du[m[1][:8]],de[m[1][8:]])
