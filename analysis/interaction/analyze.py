import numpy as np, json, random, math, sys, time, collections
D='/root/inter/'
# ---- cube model (same conventions as the Lean model) ----
B={'U':([3,0,1,2,4,5,6,7],[0]*8,[3,0,1,2,4,5,6,7,8,9,10,11],[0]*12),
   'R':([4,1,2,0,7,5,6,3],[2,0,0,1,1,0,0,2],[8,1,2,3,11,5,6,7,4,9,10,0],[0]*12),
   'F':([1,5,2,3,0,4,6,7],[1,2,0,0,2,1,0,0],[0,9,2,3,4,8,6,7,1,5,10,11],[0,1,0,0,0,1,0,0,1,1,0,0]),
   'D':([0,1,2,3,5,6,7,4],[0]*8,[0,1,2,3,5,6,7,4,8,9,10,11],[0]*12),
   'L':([0,2,6,3,4,1,5,7],[0,1,2,0,0,2,1,0],[0,1,10,3,4,5,9,7,8,2,6,11],[0]*12),
   'B':([0,1,3,7,4,5,2,6],[0,0,1,2,0,0,2,1],[0,1,2,11,4,5,6,10,8,9,3,7],[0,0,0,1,0,0,0,1,0,0,1,1])}
def mul(s,m):
    cp,co,ep,eo=s; mcp,mco,mep,meo=m
    return ([cp[mcp[i]] for i in range(8)],[(co[mcp[i]]+mco[i])%3 for i in range(8)],
            [ep[mep[i]] for i in range(12)],[(eo[mep[i]]+meo[i])%2 for i in range(12)])
ID=(list(range(8)),[0]*8,list(range(12)),[0]*12)
MV=[]
for f in 'URFDLB':
    b=B[f]; x=b
    for k in range(3):
        MV.append(x); x=mul(x,b)
NAMES=[f+p for f in 'URFDLB' for p in ['','2',"'"]]
def parse(s): return [NAMES.index(t) for t in s.split()]
def apply(s,w):
    for m in w: s=mul(s,MV[m])
    return s
H=set([0,1,2,9,10,11,4,13,7,16])
# ---- K1 tables ----
rd=lambda f:[tuple(map(int,l.split())) for l in open(D+f).read().strip().split('\n')]
eoL,coL,mL=rd('eoL.txt'),rd('coL.txt'),rd('mL.txt')
eI={k:i for i,k in enumerate(eoL)}; cI={k:i for i,k in enumerate(coL)}; sI={k:i for i,k in enumerate(mL)}
d1=np.memmap(D+'k1dist.bin',dtype=np.uint8,mode='r')
def rank1(s):
    return (eI[tuple(s[3])]*2187+cI[tuple(s[1])])*495+sI[tuple(1 if e>=8 else 0 for e in s[2])]
I0=(eI[tuple([0]*12)]*2187+cI[tuple([0]*8)])*495+sI[tuple([0]*8+[1]*4)]
# ---- K2 tables ----
cpGL=rd('cpGL.txt'); cpI={k:i for i,k in enumerate(cpGL)}
epGL=rd('epGL.txt'); epI={k:i for i,k in enumerate(epGL)}
clsT=list(map(int,open(D+'clsT.txt').read().split())); syT=list(map(int,open(D+'syT.txt').read().split()))
stabT=[list(map(int,l.split())) for l in open(D+'stabT.txt').read().split('\n')]
epCj=np.array(open(D+'epCj.txt').read().split(),dtype=np.int64)
d2=np.memmap(D+'k2dist.bin',dtype=np.uint8,mode='r')
NE=967680
SY=json.load(open('/root/kph2/syms.json'))['syms']
def inv(p): q=[0]*len(p); [q.__setitem__(p[i],i) for i in range(len(p))]; return q
SE=[(s[1],inv(s[1])) for s in SY]
def cellH(s):
    r=cpI[tuple(s[0])]; c=clsT[r]; sg,sgi=SE[syT[r]]; a=s[2]
    q=tuple(sgi[a[sg[i]]] for i in range(12)); e0=epI[q]
    e=e0
    for t in stabT[c]: e=min(e,int(epCj[e0*16+t]))
    return c*NE+e
def dH(s):
    r=cpI[tuple(s[0])]; c=clsT[r]; sg,sgi=SE[syT[r]]; a=s[2]
    q=tuple(sgi[a[sg[i]]] for i in range(12)); e0=epI[q]
    e=e0
    for t in stabT[c]: e=min(e,int(epCj[e0*16+t]))
    return int(d2[c*NE+e])
# ---- enumerate phase-1 solutions ----
def opp(f,g): return f%3==g%3 and f!=g
def phase1(s, L):
    """all canonical words of length L with s*w in H whose last move is not in H; yields (word,endstate)"""
    out=[]
    def dfs(st,r,depth,last,word):
        rk=rank1(st)
        if d1[rk]>depth: return
        if depth==0:
            if rk==I0 and (not word or word[-1] not in H): out.append((list(word),st))
            return
        if rk==I0 and depth>0 and False: pass
        for m in range(18):
            f=m//3
            if last is not None and (f==last or (opp(f,last) and f<last)): continue
            word.append(m); dfs(mul(st,MV[m]),r,depth-1,f,word); word.pop()
    dfs(s,None,L,None,[])
    return out
if __name__=='__main__':
    print('I0',I0,'d1(I0)',d1[I0], 'dH(id)',dH(ID))
