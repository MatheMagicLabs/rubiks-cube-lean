import sys,random; sys.path.insert(0,'/root/explore')
from sing import *
def rand_ord11(R):
    f=R.randrange(12); rest=[i for i in range(12) if i!=f]; R.shuffle(rest)
    ep=list(range(12))
    for k in range(11): ep[rest[k]]=rest[(k+1)%11]
    eo=[0]*12
    for i in rest[:-1]: eo[i]=R.randrange(2)
    eo[rest[-1]]=sum(eo)%2
    return (tuple(range(8)),(0,)*8,tuple(ep),tuple(eo))
def parity(p): return sum(1 for i in range(len(p)) for j in range(i) if p[j]>p[i])%2
def rand_pos(R):
    while True:
        cp=list(range(8)); R.shuffle(cp); ep=list(range(12)); R.shuffle(ep)
        if parity(cp)==parity(ep): break
    co=[R.randrange(3) for _ in range(7)]; co.append((-sum(co))%3)
    eo=[R.randrange(2) for _ in range(11)]; eo.append(sum(eo)%2)
    return (tuple(cp),tuple(co),tuple(ep),tuple(eo))
if __name__=='__main__':
    kind,n,seed,out=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]
    R=random.Random(seed); g=rand_ord11 if kind=='o11' else rand_pos
    S=[g(R) for _ in range(n)]
    if kind=='o11': assert all(order(s)==11 for s in S)
    open(out,'w').write('\n'.join(sing(s) for s in S)+'\n')
