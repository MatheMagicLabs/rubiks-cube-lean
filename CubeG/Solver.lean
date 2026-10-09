import Cube.Kph1
import Cube.Phase4
open Std
set_option compiler.extract_closed false

/-! A solver extracted from the very tables certified in the 40-move proof: Kociemba phase 1 by descent in the
distance table, then the phase-3 and phase-4 tables. Used only for an external sanity check of the model. -/

def k1Desc (d : ByteArray) : Nat → St → List Nat → List Nat × St
  | 0, x, acc => (acc.reverse, x)
  | f + 1, x, acc =>
    let i := rank x
    let v := (d.get! i).toNat
    if v == 0 then (acc.reverse, x) else
    match (List.range 18).find? (fun m => (d.get! (next i m)).toNat + 1 == v) with
    | some m => k1Desc d f (apply x m) (m :: acc)
    | none => (acc.reverse, x)

def algStr (w : List Nat) : String := " ".intercalate (w.map moveName)

def solveAllF (scrs : List String) : List String := Id.run do
  let d := distF ()
  let k3 := k3TableF ()
  let sq := sqSolveF ()
  let mut out : List String := []
  for s in scrs do
    let x0 := eval (parseAlg s)
    let (w1, x1) := k1Desc d 20 x0 []
    let w3 := match k3[(x1.cp, maskMSof x1.ep)]? with | some (some w) => w | _ => [99]
    let x3 := applyList x1 w3
    let w4 := match sq[x3]? with | some (some w) => w | _ => [99]
    let ok := applyList x0 (w1 ++ w3 ++ w4) == St.id
    out := out ++ [s ++ "\t" ++ algStr (w1 ++ w3 ++ w4) ++ "\t" ++ toString [w1.length, w3.length, w4.length] ++ "\t" ++ toString ok]
  return out
