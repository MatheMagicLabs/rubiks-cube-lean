import sys; sys.path.insert(0,'/root/explore')
from cubie import *
from sing import sing
from collections import Counter
AX=[(1,4),(0,3),(2,5)]  # (R,L),(U,D),(F,B) face indices in URFDLB
def gen(anti,powers):
    G=[]
    for a,b in AX:
        for k in powers:  # k in 0..2 means power k+1
            kb = k if anti else 2-k
            G.append(mul(MOVES[3*a+k],MOVES[3*b+kb]))
    return G
def bfs(G):
    dist={ID:0}; fr=[ID]; d=0
    while fr:
        nf=[]
        for x in fr:
            for g in G:
                y=mul(x,g)
                if y not in dist: dist[y]=d+1; nf.append(y)
        fr=nf; d+=1
    return dist
res={}
for anti in (0,1):
    for name,pw in (('quarter',[0,2]),('quarter+half',[0,1,2])):
        D=bfs(gen(anti,pw)); h=Counter(D.values())
        print('anti' if anti else 'slice',name,'order',len(D),'dist',[h[i] for i in range(max(h)+1)])
        res[(anti,name)]=D
# write all elements of each group for HTM solving
for anti in (0,1):
    D=res[(anti,'quarter+half')]
    els=sorted(D)
    open(f'grp_{"anti" if anti else "slice"}.txt','w').write('\n'.join(sing(s) for s in els)+'\n')
    import pickle; pickle.dump({s:(res[(anti,'quarter')][s],D[s]) for s in els},open(f'grp_{"anti" if anti else "slice"}.pkl','wb'))
