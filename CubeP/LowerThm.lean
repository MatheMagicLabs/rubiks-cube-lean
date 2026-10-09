import CubeG.Lower
#eval k1Witness.length
theorem k1Witness_valid : k1WitnessValid = true := by native_decide
theorem k1Low_true : k1LowF () = true := by native_decide
