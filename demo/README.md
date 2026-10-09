# Demo and witness scripts (not part of the proof library)

These were run as `CubeP.*` modules during development; move one back into `CubeP/` and `lake build CubeP.<Name>` to rerun.
- `SolveDemo.lean`: solver from the certified tables on 50 real 333.fm scrambles (`scr50.txt` → `sol50.tsv`),
  verified externally with `verify_lean_sol.py` (independent sticker simulator).
- `Kph1Hist.lean`: distance distribution of the Kociemba phase-1 table (matches Reid 1995).
- `WitnessRun.lean`, `WitnessTRun.lean`, `WitnessP2.lean`, `WitnessP3.lean`: search for the lower-bound witnesses.
