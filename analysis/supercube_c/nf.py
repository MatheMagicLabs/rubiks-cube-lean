# Normal form of the known 20-move superflip solution, in the C move numbering m = 3*face + k
# faces U0 R1 F2 D3 L4 B5; k=0 clockwise, 1 half, 2 counterclockwise
F={'U':0,'R':1,'F':2,'D':3,'L':4,'B':5}
def parse(s):
    out=[]
    for t in s.split():
        f=F[t[0]]; k=0 if len(t)==1 else (1 if t[1]=='2' else 2); out.append(3*f+k)
    return out
def show(w):
    n='URFDLB'; return ' '.join(n[m//3]+['',"2","'"][m%3] for m in w)
w0=parse("U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2")
HUD=set([0,1,2,9,10,11,4,13,7,16])
MU=[6,7,8,0,1,2,3,4,5,15,16,17,9,10,11,12,13,14]
mu=[list(range(18)),MU,[MU[MU[m]] for m in range(18)]]
isH=lambda a,m: mu[a][m] in HUD
n=len(w0); best=None
for a in range(3):
    for r in range(n):
        w=w0[r:]+w0[:r]
        t=0
        while t<n and isH(a,w[n-1-t]): t+=1
        if best is None or t>best[0]: best=(t,a,r)
t,a,r=best; w=w0[r:]+w0[:r]; w=[mu[a][m] for m in w]
print("max trailing run",t,"axis",a,"rot",r,":",show(w))
# rotate about U-D axis so that first move is on face R: y' maps F->R,R->B,B->L,L->F ; y maps F->L,L->B,B->R,R->F
yp={0:0,3:3,2:1,1:5,5:4,4:2}
def conjFace(w,mp): return [3*mp[m//3]+m%3 for m in w]
for k in range(4):
    if w[0]//3==1: break
    w=conjFace(w,yp)
print("first move on R:",show(w))
# canonical order inside s1 (opposite faces: lower index first), s1 = w[:n-t]
s1=w[:n-t]; s2=w[n-t:]
changed=True
while changed:
    changed=False
    for i in range(len(s1)-1):
        a_,b_=s1[i]//3,s1[i+1]//3
        if a_%3==b_%3 and b_<a_: s1[i],s1[i+1]=s1[i+1],s1[i]; changed=True
for i in range(len(s2)-1):
    pass
print("s1:",show(s1)," s2:",show(s2))
print("s1 codes:",' '.join(map(str,s1)))
print("s2 codes:",' '.join(map(str,s2)))
