import Cube.Square
open Std
set_option compiler.extract_closed false

#eval sqStats ()
theorem sqCheck_true : sqCheckF () = true := by native_decide

def farWord : List Nat := parseAlg "U2 R2 U2 R2 F2 R2 F2 L2 F2 U2 R2 F2 U2 B2 U2"
def farCheckW (t : HashMap St (List Nat)) : Bool := match t[eval farWord]? with
  | some v => v.length == 15 && farWord.length == 15 && farWord.all (fun m => half.contains m)
  | none => false
def farCheckF (_ : Unit) : Bool := farCheckW (sqTableF ())
theorem farCheck_true : farCheckF () = true := by native_decide
