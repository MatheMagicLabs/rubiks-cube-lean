# Merge enumeration outputs, verify words independently (K2), close signatures under symmetry, report.
import sys, glob
from sc_check import apply_word, solved, is_superflip, signature, code, decode, closure
files=sys.argv[1:]
reached={}   # len -> set of raw codes
words=[]
nodes=0
for fn in files:
    for line in open(fn):
        if line.startswith('#len'):
            parts=line.split(':'); head=parts[0].split(); L=int(head[1])
            codes=[int(x) for x in parts[1].split()] if len(parts)>1 else []
            reached.setdefault(L,set()).update(codes)
        elif line.startswith('#bound'):
            nodes+=int(line.split('nodes')[1].split()[0])
        elif '|' in line:
            w,c=line.split('|'); words.append(([int(x) for x in w.split()],int(c)))
print("files",files,"total s1 nodes",nodes)
bad=0
for w,c in words:
    if not is_superflip(apply_word(solved,w)) or code(signature(w))!=c: bad+=1
print(f"K2: re-evaluated {len(words)} printed words with the sticker model: {bad} failures")
even=[x for x in range(4096) if sum(decode(x))%2==0]
cum=set()
for L in sorted(reached):
    cl=closure(reached[L]); new=cl-cum; cum|=cl
    print(f"length {L}: raw codes {len(reached[L])}, closed {len(cl)}, new {len(new)}, cumulative {len(cum)} of {len(even)}")
un=[x for x in even if x not in cum]
print("unreached even-sum patterns:",len(un))
# orbits of unreached
seen=set(); orbs=[]
for x in un:
    if x in seen: continue
    o=closure([x]); seen|=o; orbs.append((len(o),decode(x)))
print("unreached orbits:",len(orbs))
for n,c in sorted(orbs,key=lambda t:-t[0])[:40]: print("  size",n,"rep (U R F D L B) =",c)
