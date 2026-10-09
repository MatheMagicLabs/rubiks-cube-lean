import sys
sys.path.insert(0, '/root/fmc/code')
import cube
rows = [l.rstrip('\n').split('\t') for l in open('/root/cubelean/demo/sol50.tsv') if l.strip()]
n_ok = 0; lens = []
for scr, sol, parts, ok in rows:
    st = cube.apply(cube.apply(cube.solved_state(), cube.tokens(scr)), cube.tokens(sol))
    good = cube.is_solved(st)
    L = cube.count_htm(cube.tokens(sol))
    lens.append(L); n_ok += good and L <= 40
    if not good or L > 40: print('FAIL', scr, sol, parts, ok)
print(f'{n_ok}/{len(rows)} solved by independent sticker simulator, all <= 40: lengths min {min(lens)} mean {sum(lens)/len(lens):.1f} max {max(lens)}')
