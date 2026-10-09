import Cube.Square
open Std

#eval sqSize
#eval sqMax
#eval (sqFar.map (fun p => p.2.map moveName))

theorem sqCheck_true : sqCheck = true := by native_decide

def farWord : List Nat := parseAlg "U2 R2 U2 R2 F2 R2 F2 L2 F2 U2 R2 F2 U2 B2 U2"
def farCheck : Bool := match sqTable[eval farWord]? with
  | some v => v.length == 15 && farWord.length == 15 && farWord.all (fun m => half.contains m)
  | none => false
theorem farCheck_true : farCheck = true := by native_decide
