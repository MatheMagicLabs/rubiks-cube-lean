import Cube.Phase4
theorem fiberCheck_true : fiberCheckF () = true := by native_decide
theorem sliceOk_true : sliceOk = true := by native_decide
theorem cpId_true : cpSet.contains St.id.cp = true := by native_decide
theorem pairId_true : pairSet.contains (idE, idMS) = true := by native_decide
