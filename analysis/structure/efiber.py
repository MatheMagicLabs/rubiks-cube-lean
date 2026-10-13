import numpy as np
F='/root/f28/'
d2=np.memmap('/root/inter/k2dist.bin',dtype=np.uint8,mode='r')
epLean=np.fromfile(F+'epLean.bin',dtype=np.int32)
stabOff=np.fromfile(F+'stabOff.bin',dtype=np.int32)
ssz=np.diff(stabOff)
print('classes',len(ssz),'stab sizes',np.bincount(ssz)[:20])
N=967680
spread=np.zeros(20,dtype=np.int64); spread18=np.zeros(20,dtype=np.int64)
cnt=0
# spread of distance over the 12 valid E-perms, for each (corner class, UD arrangement)
maxspread_by_min=np.zeros((19,20),dtype=np.int64)
for c in range(2768):
    if ssz[c]!=0: continue
    row=np.asarray(d2[c*N:(c+1)*N])
    R=row[epLean].reshape(40320,24).astype(np.int16)
    valid=R!=255
    assert (valid.sum(1)==12).all(), c
    mn=np.where(valid,R,99).min(1); mx=np.where(valid,R,-1).max(1)
    sp=mx-mn
    np.add.at(maxspread_by_min,(mn,sp),1)
    cnt+=1
print('classes used',cnt)
tot=maxspread_by_min.sum(0); print('spread histogram (max-min over the 12 E-perms):',{i:int(v) for i,v in enumerate(tot) if v})
for m in range(19):
    if maxspread_by_min[m].sum(): print('min',m,{i:int(v) for i,v in enumerate(maxspread_by_min[m]) if v})
