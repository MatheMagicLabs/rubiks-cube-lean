import CubeS.Sc

/-! Positive control (not used by any proof). The centre pattern (U R F D L B) = (2,3,0,2,2,1) is reached by the
20-move normal-form superflip word `3 12 1 6 2 9 7 4 16 12 1 8 17 0 4 9 7 0 4 0` found by the C search, so the
Lean search must find a word and return `false` at bound 20, and must return `true` at bound 19. -/
def ctrlSig : Sig := ⟨2, 3, 0, 2, 2, 1⟩
theorem sc_ctrl20 : scF 20 ctrlSig () = false := by native_decide
theorem sc_ctrl19 : scF 19 ctrlSig () = true := by native_decide
