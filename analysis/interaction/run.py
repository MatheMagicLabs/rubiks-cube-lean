import sys, time, random, json, math, collections
sys.setrecursionlimit(10000)
exec(open('/root/inter/analyze.py').read().split("if __name__")[0])
random.seed(7)
# ---- empirical d_H distribution of random elements of H (parity-consistent) ----
def inv_count(p): return sum(1 for i in range(len(p)) for j in range(i+1,len(p)) if p[i]>p[j])
def randH():
    while True:
        cp=random.sample(range(8),8); ud=random.sample(range(8),8); es=random.sample(range(8,12),4)
        ep=ud+es
        if (inv_count(cp)+inv_count(ep))%2==0: return (cp,[0]*8,ep,[0]*12)
hist=collections.Counter(dH(randH()) for _ in range(200000))
tot=sum(hist.values()); F={x:sum(v for k,v in hist.items() if k<=x)/tot for x in range(0,19)}
def Fx(x): return 0.0 if x<0 else (1.0 if x>18 else F[x])
def exp_min(N):
    # expected minimum of N independent draws
    return sum(1-(1-(1-Fx(x-1)))**0 for x in [])+sum((1-Fx(x-1))**N for x in range(1,19))
res={'hist_H':dict(sorted(hist.items()))}
def study(name, s, Lextra, tlimit=900):
    a=int(d1[rank1(s)]); rows=[]; best=99
    for L in range(a, a+Lextra+1):
        t=time.time(); sols=phase1(s,L)
        cells=[cellH(st) for w,st in sols]
        ds=[int(d2[c]) for c in cells]
        cellset=set(cells)
        ends=set((tuple(st[0]),tuple(st[2])) for w,st in sols)
        if ds: best=min(best, L+min(ds))
        c=collections.Counter(ds)
        rows.append({'L':L,'N':len(sols),'distinct':len(ends),'cells':len(cellset),'min':min(ds) if ds else None,
                     'mean':round(sum(ds)/len(ds),3) if ds else None,'hist':dict(sorted(c.items())),
                     'pred_min_N':round(exp_min(len(sols)),2),'pred_min_distinct':round(exp_min(len(ends)),2),'pred_min_cells':round(exp_min(len(cellset)),2),
                     'secs':round(time.time()-t,1)})
        print(name, rows[-1], flush=True)
        if time.time()-t>tlimit/8: break
    return {'name':name,'d1':a,'rows':rows,'best_total':best}
out=[]
sf=apply(ID,parse("U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2"))
kw=apply(ID,parse("L2 D2 B2 R2 D2 B2 R2 D2 R2 U2 D' B2 U' F2 U' L2 U R2 U2 B' R' F2 U2 F L2 R' D U2 L' R' U'"))
print('E[dH] random element', sum(k*v for k,v in hist.items())/tot, flush=True)
out.append(study('superflip', sf, 2))
out.append(study('k1witness', kw, 1))
for i in range(30):
    w=[random.randrange(18) for _ in range(40)]
    out.append(study(f'rand{i}', apply(ID,w), 2))
res['positions']=out
json.dump(res, open('/root/inter/result.json','w'))
print('done')
