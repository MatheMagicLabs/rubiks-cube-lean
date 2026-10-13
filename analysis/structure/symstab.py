exec(open('bad18.py').read().split("seen=set()")[0])
stab=Counter(sum(1 for s in SY if conj(s,g)==g) for g in B)
print('Bad18 stabilizer sizes (16 U-D symmetries, conjugation):',sorted(stab.items()))
stabinv=Counter(sum(1 for s in SY if conj(s,g)==g or conj(s,g)==inv(g)) for g in B)
print('with antisymmetry (s g s^-1 = g or g^-1):',sorted(stabinv.items()))
# baseline: random elements of H
import random; random.seed(5)
from cubie import MOVES, mul as fmul, ID
HM=[0,1,2,9,10,11,4,7,13,16]
cnt=Counter()
for t in range(20000):
    x=ID
    for k in range(40): x=fmul(x,MOVES[random.choice(HM)])
    g=(x[0],x[2]); cnt[sum(1 for s in SY if conj(s,g)==g)]+=1
print('random H elements stabilizer sizes:',sorted(cnt.items()))
