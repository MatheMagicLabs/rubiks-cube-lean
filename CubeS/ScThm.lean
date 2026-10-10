import CubeS.Sc

/-! Supercube certificate: no normal-form word of length ≤ 21 solves the superflip with all centre
quarter-turn counts ≡ 0 (mod 4). Used by `CubeP.ScProof.supercube_superflip`. -/
theorem sc_true : scF 21 sig0 () = true := by native_decide
