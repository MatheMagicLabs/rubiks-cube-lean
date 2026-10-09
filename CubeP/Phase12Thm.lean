import Cube.Phase12
#eval stats ()
theorem eoCheck_true : eoCheck = true := by native_decide
theorem k2Check_true : k2CheckF () = true := by native_decide
theorem g1KeepsEO_true : g1KeepsEO = true := by native_decide
