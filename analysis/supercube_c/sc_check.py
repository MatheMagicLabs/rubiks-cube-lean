# Independent checks for the supercube enumeration: sticker-level evaluation (K2) and symmetry closure of signatures.
import itertools, sys
import numpy as np
FACES='URFDLB'
N={'U':(0,1,0),'R':(1,0,0),'F':(0,0,1),'D':(0,-1,0),'L':(-1,0,0),'B':(0,0,-1)}
NI={v:k for k,v in N.items()}
stickers=[]
for p in itertools.product((-1,0,1),repeat=3):
    for f,n in N.items():
        if all(p[i]==n[i] for i in range(3) if n[i]!=0) and sum(abs(x) for x in p)>0:
            stickers.append((p,n))
assert len(stickers)==54
sid={s:i for i,s in enumerate(stickers)}
def rot_cw(n):
    # rotation by -90 deg about axis n (clockwise seen from outside along n)
    a=np.array(n); K=np.array([[0,-a[2],a[1]],[a[2],0,-a[0]],[-a[1],a[0],0]])
    R=np.eye(3)+np.sin(-np.pi/2)*K+(1-np.cos(-np.pi/2))*K@K
    return np.rint(R).astype(int)
def perm_for(face):
    n=N[face]; R=rot_cw(n); P=list(range(54))
    for i,(p,s) in enumerate(stickers):
        if sum(p[j]*n[j] for j in range(3))==1:
            q=tuple(int(x) for x in R@np.array(p)); t=tuple(int(x) for x in R@np.array(s)); P[i]=sid[(q,t)]
    return P
MP={f:perm_for(f) for f in FACES}
def apply_word(col, w):
    for m in w:
        f=FACES[m//3]; k=m%3+1 if m%3<2 else 3   # k quarter turns: 0->1, 1->2, 2->3
        for _ in range(k):
            P=MP[f]; new=[None]*54
            for i in range(54): new[P[i]]=col[i]
            col=new
    return col
solved=[NI[s] for (p,s) in stickers]
def is_superflip(col):
    for i,(p,s) in enumerate(stickers):
        nz=sum(1 for x in p if x!=0)
        if nz==2:   # edge sticker: must show the other face of the same edge
            other=[q for q in N if N[q]!=s and all((N[q][j]==p[j]) for j in range(3) if N[q][j]!=0)]
            if col[i]!=other[0]: return False
        else:
            if col[i]!=NI[s]: return False
    return True
def signature(w):
    c=[0]*6
    for m in w: c[m//3]=(c[m//3]+(1,2,3)[m%3])%4
    return c
def code(c): return sum(c[f]*4**f for f in range(6))
def decode(x): return [(x//4**f)%4 for f in range(6)]
# symmetry action on signatures: 48 signed permutation matrices
mats=[]
for perm in itertools.permutations(range(3)):
    for signs in itertools.product((1,-1),repeat=3):
        A=np.zeros((3,3),int)
        for i in range(3): A[i][perm[i]]=signs[i]
        mats.append(A)
def act(A,c):
    d=int(round(np.linalg.det(A))); out=[0]*6
    for fi,f in enumerate(FACES):
        g=NI[tuple(int(x) for x in A@np.array(N[f]))]; out[FACES.index(g)]=(d*c[fi])%4
    return out
def closure(codes):
    S=set()
    for x in codes:
        c=decode(x)
        for A in mats:
            y=act(A,c); S.add(code(y)); S.add(code([(-v)%4 for v in y]))
    return S
if __name__=='__main__':
    # self-test: known solution
    w0=[0,4,6,15,3,16,3,1,12,16,3,2,11,4,6,5,12,16,1,7]   # U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2
    print("w0 is superflip:",is_superflip(apply_word(solved,w0)), "sig",signature(w0))
    wn=[5,14,1,15,2,9,7,4,16,3,1,6,15,0,7,0,4,9,7,0]
    print("normal form is superflip:",is_superflip(apply_word(solved,wn)),"sig",signature(wn),"code",code(signature(wn)))
    print("orbit of code 946 contains w0's code:", code(signature(w0)) in closure([946]), " orbit size", len(closure([946])))
    print("even-sum patterns:", sum(1 for x in range(4096) if sum(decode(x))%2==0))
