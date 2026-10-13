import sys,numpy as np; sys.path.insert(0,'/root/explore')
from collections import Counter
exec(open('hparts.py').read().split("B=[]")[0])   # dc, du, de dictionaries (BFS on components)
F='/root/f28/'; D='/root/inter/'
cpGL=np.fromfile(F+'cpGL.bin',dtype=np.uint8).reshape(-1,8); epGL=np.fromfile(F+'epGL.bin',dtype=np.uint8).reshape(-1,12)
repsT=np.fromfile(F+'repsT.bin',dtype=np.int32); stabOff=np.fromfile(F+'stabOff.bin',dtype=np.int32); ssz=np.diff(stabOff)
print(cpGL.shape,epGL.shape,repsT.shape, repsT[:5])
duA=np.array([du[tuple(int(x) for x in e[:8])] for e in epGL],dtype=np.int16)
deA=np.array([de[tuple(int(x) for x in e[8:])] for e in epGL],dtype=np.int16)
N=967680; fh=open(D+'k2dist.bin','rb')
HS=np.zeros((19,40),dtype=np.int64); HM=np.zeros((19,20),dtype=np.int64)
for c in range(2768):
    if ssz[c]!=0: continue
    dcv=dc[tuple(int(x) for x in cpGL[repsT[c]])]
    fh.seek(c*N); row=np.frombuffer(fh.read(N),dtype=np.uint8).astype(np.int16); v=row!=255
    S=dcv+duA+deA; M=np.maximum(np.maximum(duA,deA),dcv)
    np.add.at(HS,(row[v],S[v]),1); np.add.at(HM,(row[v],M[v]),1)
np.save('HS.npy',HS); np.save('HM.npy',HM)
print('d_H  min/mean/max of (dC+dUD+dE)   |  fraction with d_H > sum')
for d in range(19):
    r=HS[d]; n=r.sum()
    if n==0: continue
    idx=np.nonzero(r)[0]; mean=(r*np.arange(40)).sum()/n
    print(d, idx.min(), round(mean,2), idx.max(), '| frac d>sum', round(r[:d].sum()/n,6), ' frac d<max', round(HM[d][d+1:].sum()/n,6))
