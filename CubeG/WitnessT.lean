import CubeG.Witness
open Std
set_option compiler.extract_closed false

def lenOf (o : Option (Option (List Nat))) : Nat := match o with | some (some w) => w.length | _ => 99

def fixParity (cp ep : Array Nat) (a b : Nat) : Array Nat :=
  if (inv cp.toList + inv ep.toList) % 2 == 0 then ep else (ep.set! a ep[b]!).set! b ep[a]!

def witnessTF (_ : Unit) : List String := Id.run do
  let k2 := k2TableF ()
  let k3 := k3TableF ()
  let sq := sqSolveF ()
  let finish (x : St) : List Nat :=
    let w3 := match k3[(x.cp, maskMSof x.ep)]? with | some (some w) => w | _ => [99]
    let x3 := applyList x w3
    let w4 := match sq[x3]? with | some (some w) => w | _ => [99]
    w3 ++ w4
  let mut out : List String := []
  -- phase 1: superflip
  out := out ++ [s!"P1 superflip eo-dist {lenOf (some (eoTable[(eval superflip).eo]?.getD none))}"]
  -- phase 3
  let some (k, _) := k3.toList.find? (fun p => lenOf (some p.2) == 13) | return out ++ ["no k3"]
  let cp := k.1
  let ms := k.2
  let ep0 := Id.run do
    let mut a : Array Nat := Array.replicate 12 0; let mut mi := 0; let mut si := 0
    for j in [0:12] do
      if j ≥ 8 then a := a.set! j j
      else if ms[j]! == 1 then a := a.set! j ([1,3,5,7][mi]!); mi := mi + 1
      else a := a.set! j ([0,2,4,6][si]!); si := si + 1
    return a
  let ep := fixParity cp ep0 0 2
  let x3 : St := ⟨cp, St.id.co, ep, St.id.eo⟩
  let W3 := finish x3
  let w3 := invWord W3
  out := out ++ [s!"P3 key-dist {lenOf k3[(cp, ms)]?} solved {applyList x3 W3 == St.id} w0ok {eval w3 == x3} w0: {algStr w3}"]
  -- phase 2
  let some (k', _) := k2.toList.find? (fun p => lenOf (some p.2) == 10) | return out ++ ["no k2"]
  let ep2 := Id.run do
    let mut a : Array Nat := Array.replicate 12 0; let mut hi := 8; let mut lo := 0
    for j in [0:12] do
      if k'.2[j]! == 1 then a := a.set! j hi; hi := hi + 1 else a := a.set! j lo; lo := lo + 1
    return a
  let cp2 : Array Nat := #[0,1,2,3,4,5,6,7]
  let x2 : St := ⟨cp2, k'.1, fixParity cp2 ep2 0 1, St.id.eo⟩
  let w2 := match k2[(x2.co, maskOf x2.ep)]? with | some (some w) => w | _ => [99]
  let W2 := w2 ++ finish (applyList x2 w2)
  let wit2 := invWord W2
  out := out ++ [s!"P2 key-dist {lenOf k2[(x2.co, maskOf x2.ep)]?} solved {applyList x2 W2 == St.id} w0ok {eval wit2 == x2} w0: {algStr wit2}"]
  return out
