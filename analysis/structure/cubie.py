# Kociemba cubie model: state = (cp, co, ep, eo); mul(a,b) = apply a then b
CP={'U':[3,0,1,2,4,5,6,7],'R':[4,1,2,0,7,5,6,3],'F':[1,5,2,3,0,4,6,7],'D':[0,1,2,3,5,6,7,4],'L':[0,2,6,3,4,1,5,7],'B':[0,1,3,7,4,5,2,6]}
CO={'U':[0]*8,'R':[2,0,0,1,1,0,0,2],'F':[1,2,0,0,2,1,0,0],'D':[0]*8,'L':[0,1,2,0,0,2,1,0],'B':[0,0,1,2,0,0,2,1]}
EP={'U':[3,0,1,2,4,5,6,7,8,9,10,11],'R':[8,1,2,3,11,5,6,7,4,9,10,0],'F':[0,9,2,3,4,8,6,7,1,5,10,11],'D':[0,1,2,3,5,6,7,4,8,9,10,11],'L':[0,1,10,3,4,5,9,7,8,2,6,11],'B':[0,1,2,11,4,5,6,10,8,9,3,7]}
EO={'U':[0]*12,'R':[0]*12,'F':[0,1,0,0,0,1,0,0,1,1,0,0],'D':[0]*12,'L':[0]*12,'B':[0,0,0,1,0,0,0,1,0,0,1,1]}
ID=(tuple(range(8)),(0,)*8,tuple(range(12)),(0,)*12)
def mul(a,b):
    return (tuple(a[0][b[0][i]] for i in range(8)), tuple((a[1][b[0][i]]+b[1][i])%3 for i in range(8)),
            tuple(a[2][b[2][i]] for i in range(12)), tuple((a[3][b[2][i]]+b[3][i])%2 for i in range(12)))
def inv(a):
    cp=[0]*8;co=[0]*8;ep=[0]*12;eo=[0]*12
    for i in range(8): cp[a[0][i]]=i
    for i in range(8): co[i]=(-a[1][cp[i]])%3
    for i in range(12): ep[a[2][i]]=i
    for i in range(12): eo[i]=a[3][ep[i]]
    return (tuple(cp),tuple(co),tuple(ep),tuple(eo))
FACES='URFDLB'
MOVES=[]
for f in FACES:
    b=(tuple(CP[f]),tuple(CO[f]),tuple(EP[f]),tuple(EO[f])); x=b
    for k in range(3): MOVES.append(x); x=mul(x,b)
MNAME=[f+s for f in FACES for s in ['',"2","'"]]
def parse(s):
    w=[]
    for t in s.split():
        f=FACES.index(t[0]); p={'':0,'2':1,"'":2}[t[1:]]; w.append(3*f+p)
    return w
def ev(w,s=ID):
    for m in w: s=mul(s,MOVES[m])
    return s
def order(a):
    x=a;n=1
    while x!=ID: x=mul(x,a); n+=1
    return n
def cycles(p):
    seen=set();cs=[]
    for i in range(len(p)):
        if i in seen: continue
        c=[];j=i
        while j not in seen: seen.add(j);c.append(j);j=p[j]
        cs.append(c)
    return cs
if __name__=='__main__':
    assert order(MOVES[0])==4 and order(ev(parse("R U")))==105
    sf=ev(parse("U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2"))
    print('superflip check',sf[3],sf[0],sf[2])
    print('max order example R U2 D\' B D\'',order(ev(parse("R U2 D' B D'"))))
