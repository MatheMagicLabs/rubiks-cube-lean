import CubeG.Solver
import CubeG.Lower
import Cube.Parity
open Std
set_option compiler.extract_closed false

def invMove (m : Nat) : Nat := 3 * (m / 3) + (2 - m % 3)
def invWord (w : List Nat) : List Nat := (w.reverse).map invMove

def stOfCell (i : Nat) : St :=
  let re := i / (2187 * 495); let rc := (i / 495) % 2187; let rs := i % 495
  let e := eoL.find? (fun k => eIdx[k]! == re) |>.getD #[]
  let c := coL.find? (fun k => cIdx[k]! == rc) |>.getD #[]
  let s := mL.find? (fun k => sIdx[k]! == rs) |>.getD #[]
  let ep := Id.run do
    let mut a : Array Nat := #[]; let mut hi := 8; let mut lo := 0
    for j in [0:12] do
      if s[j]! == 1 then a := a.push hi; hi := hi + 1 else a := a.push lo; lo := lo + 1
    return a
  let cp0 : Array Nat := #[0,1,2,3,4,5,6,7]
  let cp := if (inv cp0.toList + inv ep.toList) % 2 == 0 then cp0 else #[1,0,2,3,4,5,6,7]
  ⟨cp, c, ep, e⟩

def witnessF (_ : Unit) : List String := Id.run do
  let d := distF ()
  let k3 := k3TableF ()
  let sq := sqSolveF ()
  let mut out : List String := []
  let mut found := 0
  let mut i := 0
  while found < 3 && i < NN do
    if (d.get! i).toNat == 12 then
      let x := stOfCell i
      let (w1, x1) := k1Desc d 20 x []
      let w3 := match k3[(x1.cp, maskMSof x1.ep)]? with | some (some w) => w | _ => [99]
      let x3 := applyList x1 w3
      let w4 := match sq[x3]? with | some (some w) => w | _ => [99]
      let W := w1 ++ w3 ++ w4
      let ok := applyList x W == St.id
      let w0 := invWord W
      let chk := rank (eval w0) == i && eval w0 == x
      out := out ++ [s!"cell {i} rankOk {rank x == i} solved {ok} w0ok {chk} len {w0.length} w0: {algStr w0}"]
      found := found + 1
    i := i + 1
  return out
