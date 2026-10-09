import Cube.Phase34
import Cube.Select
open Std
set_option compiler.extract_closed false

/-! Phase 4: solving table for the square group, and the fiber check: every state with oriented pieces, corner
permutation in H, every edge in its home slice and even edge permutation lies in the table. -/

def sqSolveF (_ : Unit) : HashMap St (Option (List Nat)) :=
  solveTable St.id apply half half (fun x => x == St.id) 15

def sliceSets : List (List Nat) :=
  [[0,2,4,6],[1,3,5,7],[0,2,4,6],[1,3,5,7],[0,2,4,6],[1,3,5,7],[0,2,4,6],[1,3,5,7],
   [8,9,10,11],[8,9,10,11],[8,9,10,11],[8,9,10,11]]

def zeros8 : Array Nat := St.id.co
def zeros12 : Array Nat := St.id.eo

def solOk (x : St) (o : Option (Option (List Nat))) : Bool :=
  match o with
  | some (some w) => decide (w.length ≤ 15) && w.all (fun m => half.contains m) && decide (applyList x w = St.id)
  | _ => false

def fiberPW (t : HashMap St (Option (List Nat))) (l : List Nat) : Bool :=
  (inv l % 2 != 0) || hList.all (fun cp => solOk ⟨cp, zeros8, l.toArray, zeros12⟩ t[(⟨cp, zeros8, l.toArray, zeros12⟩ : St)]?)

def fiberCheckW (t : HashMap St (Option (List Nat))) : Bool := allSel sliceSets [] (fiberPW t)
def fiberCheckF (_ : Unit) : Bool := fiberCheckW (sqSolveF ())

def sliceOk : Bool := (List.range 12).all (fun i => (List.range 12).all (fun e =>
  !(cls e == idE[i]! && clsM e == idMS[i]!) || (sliceSets[i]!).contains e))
