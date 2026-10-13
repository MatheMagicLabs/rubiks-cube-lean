from cubie import *
CF=['URF','UFL','ULB','UBR','DFR','DLF','DBL','DRB']; EF=['UR','UF','UL','UB','DR','DF','DL','DB','FR','FL','BL','BR']
SMP="UF UR UB UL DF DR DB DL FR FL BR BL UFR URB UBL ULF DRF DFL DLB DBR".split()
def sing(s):
    cp,co,ep,eo=s; out=[]
    for name in SMP:
        if len(name)==2:
            i=[k for k,e in enumerate(EF) if set(e)==set(name)][0]
            out.append(''.join(EF[ep[i]][(EF[i].index(f)+eo[i])%2] for f in name))
        else:
            i=[k for k,c in enumerate(CF) if set(c)==set(name)][0]
            out.append(''.join(CF[cp[i]][(CF[i].index(f)-co[i])%3] for f in name))
    return ' '.join(out)
def nx2w(line):  # nxopt solution like ' U3 R1 B3' -> word
    w=[]
    for t in line.split():
        f=FACES.index(t[0]); w.append(3*f+int(t[1])-1)
    return w
