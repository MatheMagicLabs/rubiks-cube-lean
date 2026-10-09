import CubeG.WitnessT
open Std
def witnessP3 : List String := Id.run do
  let k3 := k3TableF ()
  let sq := sqSolveF ()
  let cands := (k3.toList.filter (fun p => lenOf (some p.2) == 13)).take 5
  let mut out : List String := []
  for (k, _) in cands do
    let cp := k.1
    let ms := k.2
    let ep0 := Id.run do
      let mut a : Array Nat := Array.replicate 12 0; let mut mi := 0; let mut si := 0
      for j in [0:12] do
        if j ≥ 8 then a := a.set! j j
        else if ms[j]! == 1 then a := a.set! j ([1,3,5,7][mi]!); mi := mi + 1
        else a := a.set! j ([0,2,4,6][si]!); si := si + 1
      return a
    let ep := fixParity cp ep0 8 9
    let x3 : St := ⟨cp, St.id.co, ep, St.id.eo⟩
    let w3 := match k3[(x3.cp, maskMSof x3.ep)]? with | some (some w) => w | _ => [99]
    let x4 := applyList x3 w3
    let w4 := match sq[x4]? with | some (some w) => w | _ => [99]
    let W := w3 ++ w4
    let wit := invWord W
    out := out ++ [s!"P3 dist {lenOf k3[((eval wit).cp, maskMSof (eval wit).ep)]?} solved {applyList x3 W == St.id} w0ok {eval wit == x3} w0: {algStr wit}"]
  return out
#eval witnessP3
