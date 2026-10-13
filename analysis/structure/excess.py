import sys,numpy as np; sys.path.insert(0,'/root/explore')
exec(open('interact.py').read().split("N=967680")[0])
N=967680; fh=open(D+'k2dist.bin','rb'); ex=[]; hist=Counter()
for c in range(2768):
    if ssz[c]!=0: continue
    cp=tuple(int(x) for x in cpGL[repsT[c]]); dcv=dc[cp]
    fh.seek(c*N); row=np.frombuffer(fh.read(N),dtype=np.uint8).astype(np.int16); v=row!=255
    X=row-(dcv+duA+deA); X[~v]=-99
    for k,cnt in zip(*np.unique(X[v],return_counts=True)): hist[int(k)]+=int(cnt)
    for e in np.nonzero(X>=7)[0][:3]: ex.append((int(X[e]),int(row[e]),cp,tuple(int(x) for x in epGL[e]),dcv,int(duA[e]),int(deA[e])))
print('excess d_H-(dC+dUD+dE) histogram (cells, trivial-stabilizer classes):',sorted(hist.items()))
ex.sort(reverse=True)
for x in ex[:10]: print(x)
