# Rubik's cube bounds in Lean 4

Machine-checked bounds on the 3×3×3 Rubik's cube and related puzzles, in plain Lean 4 (no Mathlib).
Large finite facts are proved by `native_decide` certificates; everything around them is ordinary Lean proof.

Author: Vincent Weinreich.

## Main results (half-turn metric, 18 face turns)

| Theorem | File | Statement |
|---|---|---|
| `gods_number_bounds` | `CubeP/SfProof.lean` | **20 ≤ God's number ≤ 28**: every reachable position is solved in ≤ 28 turns, and the superflip needs 20 |
| `upper_bound_28` | `CubeP/K28Proof.lean` | every reachable position is solved in ≤ 28 turns |
| `superflip_distance` | `CubeP/SfProof.lean` | the superflip is at distance exactly 20 |
| `upper_bound_30` | `CubeP/Kph2Proof.lean` | Kociemba phase 1 (≤ 12) + phase 2 (≤ 18) |
| `upper_bound_40` | `CubeP/Final40.lean` | Kociemba phase 1 + Thistlethwaite phases 3, 4 |
| `thistlethwaite_45` | `CubeP/Final.lean` | Thistlethwaite's 45-move algorithm |
| `kociemba_phase1`, `kociemba_phase1_lower` | `CubeP/Kph1Proof.lean`, `CubeP/LowerProof.lean` | phase 1 needs exactly 12 in the worst case |
| `kociemba_phase2`, `kociemba_phase2_lower`, `kociemba_phase2_attained` | `CubeP/Kph2Proof.lean`, `CubeP/Low2Proof.lean` | phase 2 needs exactly 18 in the worst case |
| `thistle_phase{1,2,3}_lower` | `CubeP/LowerTProof.lean` | worst-case lower bounds for Thistlethwaite's phases |
| `supercube_superflip`, `supercube_gods_number_ge_22` | `CubeP/ScProof.lean`, `CubeP/ScFinal.lean` | **supercube**: the superflip with all centres at home needs 22 turns, so God's number of the supercube is ≥ 22 |
| `order11_lower`, `order11_witness` | `CubeP/Ord11Proof.lean` | the shortest word producing an element of order 11 has 10 turns |
| `square_group_gods_number` | `CubeP/SquareProof.lean` | God's number of the square group ⟨U2,R2,F2,D2,L2,B2⟩ is 15 |
| `slice_group_*`, `antislice_group_*` | `CubeP/SliceProof.lean` | God's numbers of the slice and antislice groups |
| `pocket_cube_htm`, `pocket_cube_qtm` | `CubeP/GodsProof.lean` | 2×2×2: God's number 11 (HTM) and 14 (QTM) |
| `parity_law` | `Cube/ParityLaw.lean` | every reachable position has equal corner and edge permutation parity |

"Reachable" means `eval w` for a word `w` of face turns (`m < 18`); the cube model is `St` in `Cube/Model.lean`
(corner/edge permutation and orientation arrays).

## Trust base

`#print axioms` for the main theorems gives `propext, Classical.choice, Quot.sound` plus
`Lean.ofReduceBool, Lean.trustCompiler` (from `native_decide`), i.e. the Lean kernel plus the compiler that evaluates
the certificates. Recorded outputs are in `demo/*axioms*.log`.

What is checked by tests rather than proofs: that `St` and the move tables describe the physical cube. The
solver was validated on 50 real scrambles against an independent sticker simulator (`demo/verify_lean_sol.py`), and
table statistics match published data (e.g. Reid's phase-1 distribution).

## Building

Lean `v4.23.0` (see `lean-toolchain`), no dependencies.

```
lake build            # model and solver library
lake build CubeP      # all proofs and certificates
```

The certificates are heavy. Recorded wall-clock times:

| Module | Time | Peak memory |
|---|---|---|
| `CubeP.K28ThmA/B1/B2/C` (28-move bound) | ≈ 2.4 h total | |
| `CubeP.Low2ThmB` (phase-2 lower bound) | ≈ 2.2 h | |
| `CubeS.ScThm` (supercube, `sc_true`) | ≈ 8.9 h | ≈ 5.7 GB |
| everything else | minutes | |

Build heavy modules one at a time on machines with < 8 GB RAM (`demo/rebuild.sh` does this).

## Layout

- `Cube/` — model, moves, parity law, Thistlethwaite/Kociemba phase machinery
- `CubeG/`, `CubeH/`, `CubeK/`, `CubeO/`, `CubeS/` — precompiled search and table code used by the certificates
- `CubeP/` — proofs; `*Thm.lean` files hold the `native_decide` certificates, `*Proof.lean` the theorems
- `demo/` — build logs, axiom logs, witness searches and the external validation script (not part of the proof)

## License

MIT
