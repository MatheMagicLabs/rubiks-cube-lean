# Unverified analysis code

Research code behind the statements in the paper that are **not** Lean theorems: C prototypes of the searches, the
measurements in the appendices, and the coset runs mentioned in the conclusion. Nothing here is part of the proof.
Paths inside the scripts are those of the original machine (`/root/...`, `/home/claude/...`); several scripts read
tables dumped from the Lean build (`demo/lean/DumpK1.lean`, `DumpK2.lean`) or Rokicki's `cube20src`.

| Folder | Paper | Content |
|---|---|---|
| `superflip_c/` | Sec. "The superflip needs 20 moves" | C prototypes of the normal-form search (`proto*.c`), run log |
| `supercube_c/` | Sec. "The supercube" | C search with centre pattern (`proto_sc.c` unreduced, `proto_sc3.c` with mirror/x2 reduction, used for bound 21), trace of the positive control, logs and found words for bounds 20 and 21, re-check and pattern-closure scripts |
| `interaction/` | Appendix A | phase-1 solution enumeration and phase-2 lengths of their endpoints (`run.py`, `analyze.py`), results |
| `structure/` | Appendix B | element orders and Sylow counts, order-11 search, hardest phase-2 elements, slice groups, pre-registration (`prereg_struktur.md` with SHA-256) |
| `coset_c/` | Conclusion | coset solver (`coset.c`), Lipschitz cover of the phase-1 coset graph (`cover.c`), logs: one coset solved to depth 21 in 773 s; 69 centres cover all cosets needed for 27 |
