import Cube.Phase34
open Std
set_option compiler.extract_closed false

/-! Kociemba's phase 1 (G0 → <U,D,R2,L2,F2,B2>) as one coordinate space of 2048 · 2187 · 495 = 2,217,093,120
cells: edge orientation × corner orientation × E-slice positions. A full distance table is held in a ByteArray; the
certificate check below is what the proof uses. -/

def eoSet : HashMap (Array Nat) Unit := closure eoZero eoAct allMoves
def coSet : HashMap (Array Nat) Unit := closure St.id.co coAct allMoves
def mSet : HashMap (Array Nat) Unit := closure idE maskAct allMoves

def mkIdx (l : List (Array Nat)) : HashMap (Array Nat) Nat :=
  (l.zipIdx).foldl (fun h p => h.insert p.1 p.2) ∅

def eoL : List (Array Nat) := eoSet.toList.map Prod.fst
def coL : List (Array Nat) := coSet.toList.map Prod.fst
def mL : List (Array Nat) := mSet.toList.map Prod.fst
def eIdx : HashMap (Array Nat) Nat := mkIdx eoL
def cIdx : HashMap (Array Nat) Nat := mkIdx coL
def sIdx : HashMap (Array Nat) Nat := mkIdx mL

def mkTab (l : List (Array Nat)) (idx : HashMap (Array Nat) Nat) (act : Array Nat → Nat → Array Nat) : Array Nat :=
  Id.run do
    let mut t : Array Nat := Array.replicate (l.length * 18) 0
    for k in l do
      for m in [0:18] do
        t := t.set! (idx[k]! * 18 + m) idx[act k m]!
    return t

def TE : Array Nat := mkTab eoL eIdx eoAct
def TC : Array Nat := mkTab coL cIdx coAct
def TS : Array Nat := mkTab mL sIdx maskAct

/-- table check for one component: every listed value has an index below `n`, and the move table is right. -/
def tabOk (l : List (Array Nat)) (idx : HashMap (Array Nat) Nat) (act : Array Nat → Nat → Array Nat) (t : Array Nat)
    (n : Nat) (k0 : Array Nat) : Bool :=
  l.all (fun k => match idx[k]? with
    | some r => decide (r < n) && (List.range 18).all (fun m => idx[act k m]? == some t[r * 18 + m]!) &&
        (r != idx[k0]! || k == k0)
    | none => false) && idx.contains k0

def eoClosed : Bool := eoSet.toList.all (fun p => allMoves.all (fun m => eoSet.contains (eoAct p.1 m)))
def coClosed : Bool := coSet.toList.all (fun p => allMoves.all (fun m => coSet.contains (coAct p.1 m)))
def mClosed : Bool := mSet.toList.all (fun p => allMoves.all (fun m => mSet.contains (maskAct p.1 m)))
def compOk : Bool := eoClosed && coClosed && mClosed &&
  eoSet.contains eoZero && coSet.contains St.id.co && mSet.contains idE &&
  tabOk eoL eIdx eoAct TE 2048 eoZero && tabOk coL cIdx coAct TC 2187 St.id.co && tabOk mL sIdx maskAct TS 495 idE

def NN : Nat := 2048 * 2187 * 495
def rank (x : St) : Nat := (eIdx[x.eo]! * 2187 + cIdx[x.co]!) * 495 + sIdx[maskOf x.ep]!
def i0 : Nat := (eIdx[eoZero]! * 2187 + cIdx[St.id.co]!) * 495 + sIdx[idE]!

@[inline] def next (i m : Nat) : Nat :=
  (TE[(i / (2187 * 495)) * 18 + m]! * 2187 + TC[((i / 495) % 2187) * 18 + m]!) * 495 + TS[(i % 495) * 18 + m]!

def distF (_ : Unit) : ByteArray := Id.run do
  let mut d := ByteArray.emptyWithCapacity NN
  for _ in [0:NN] do d := d.push 255
  d := d.set! i0 0
  for depth in [0:12] do
    let dv := depth.toUInt8
    for i in [0:NN] do
      if d.get! i == dv then
        for m in [0:18] do
          let j := next i m
          if d.get! j == 255 then d := d.set! j (dv + 1)
  return d

def anyMove (d : ByteArray) (i v : Nat) : Nat → Bool
  | 0 => false
  | m + 1 => if (d.get! (next i m)).toNat + 1 == v then true else anyMove d i v m

def cellOk (d : ByteArray) (i : Nat) : Bool :=
  let v := (d.get! i).toNat
  decide (v ≤ 12) && (v != 0 || i == i0) && (v == 0 || anyMove d i v 18)

def chkFrom (d : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => if cellOk d n then chkFrom d n else false

def kCheckF (_ : Unit) : Bool := chkFrom (distF ()) NN

def histF (_ : Unit) : List Nat := Id.run do
  let d := distF ()
  let mut h : Array Nat := Array.replicate 256 0
  for i in [0:NN] do
    let v := (d.get! i).toNat
    h := h.set! v (h[v]! + 1)
  return (h.toList.take 13) ++ [h[255]!]
