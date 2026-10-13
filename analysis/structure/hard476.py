from collections import Counter
D='/root/inter/'
rd=lambda f:[tuple(map(int,l.split())) for l in open(D+f).read().strip().split('\n')]
eoL,coL,mL=rd('eoL.txt'),rd('coL.txt'),rd('mL.txt')
print(len(eoL),len(coL),len(mL))
cells=[];n12=[]
for l in open('/root/f28/m12w.out'):
    if l.startswith('OK12'):
        p=l.split(); cells.append(int(p[1])); n12.append(int(p[2].split('=')[1]))
print('cells',len(cells))
def dec(i):
    s=i%495; r=i//495; return eoL[r//2187],coL[r%2187],mL[s]
st=[dec(i) for i in cells]
print('flipped edges',Counter(sum(e) for e,c,m in st))
print('twisted corners',Counter(sum(1 for x in c if x) for e,c,m in st))
print('twist pattern (#cw,#ccw)',Counter((c.count(1),c.count(2)) for e,c,m in st))
print('E-edges inside E-slice',Counter(sum(m[8:]) for e,c,m in st))
print('example m',st[0][2])
print('n12 (phase-1 words of length 12)',Counter(n12))
# flipped pattern: which positions; E slice positions are 8..11
print('flips in U layer, D layer, E layer',Counter((sum(e[0:4]),sum(e[4:8]),sum(e[8:12])) for e,c,m in st).most_common(10))
print('E-edge positions (U,D,E counts)',Counter((sum(m[0:4]),sum(m[4:8]),sum(m[8:12])) for e,c,m in st))
# superflip-like?
print('all flipped',sum(1 for e,c,m in st if sum(e)==12))
