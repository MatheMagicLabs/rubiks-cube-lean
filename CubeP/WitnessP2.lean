import CubeG.WitnessT
open Std
def witnessP2 : List String := Id.run do
  let k2 := k2TableF ()
  let k3 := k3TableF ()
  let sq := sqSolveF ()
  let finish (x : St) : List Nat :=
    let w3 := match k3[(x.cp, maskMSof x.ep)]? with | some (some w) => w | _ => [99]
    let x3 := applyList x w3
    let w4 := match sq[x3]? with | some (some w) => w | _ => [99]
    w3 ++ w4
  let some (k', _) := k2.toList.find? (fun p => lenOf (some p.2) == 10) | return ["no k2"]
  let ep2 := Id.run do
    let mut a : Array Nat := Array.replicate 12 0; let mut hi := 8; let mut lo := 0
    for j in [0:12] do
      if k'.2[j]! == 1 then a := a.set! j hi; hi := hi + 1 else a := a.set! j lo; lo := lo + 1
    return a
  let cp0 : Array Nat := #[0,1,2,3,4,5,6,7]
  let cp2 := if (inv cp0.toList + inv ep2.toList) % 2 == 0 then cp0 else #[1,0,2,3,4,5,6,7]
  let x2 : St := ⟨cp2, k'.1, ep2, St.id.eo⟩
  let w2 := match k2[(x2.co, maskOf x2.ep)]? with | some (some w) => w | _ => [99]
  let W2 := w2 ++ finish (applyList x2 w2)
  let wit := invWord W2
  return [s!"P2 key-dist {lenOf k2[(x2.co, maskOf x2.ep)]?} solved {applyList x2 W2 == St.id} w0ok {eval wit == x2} eo {(eval wit).eo == eoZero} w0: {algStr wit}"]
#eval witnessP2
