import Cube.Kph1
import Cube.Phase4
open Std
set_option compiler.extract_closed false

/-! Kociemba's phase 2: God's number of the domino group <U,D,R2,L2,F2,B2> acting on (corner, edge) permutations,
with the 16 symmetries that fix the U-D axis. Cells: (symmetry class of the corner permutation) × (edge permutation),
2768 · 967680 cells. -/

abbrev P := Array Nat × Array Nat
def epAct (e : Array Nat) (m : Nat) : Array Nat := (List.range 12).toArray.map (fun i => e[(moves[m]!).ep[i]!]!)
def pAct (p : P) (m : Nat) : P := (cpAct p.1 m, epAct p.2 m)
def pActList (p : P) (w : List Nat) : P := w.foldl pAct p
def idP : P := (St.id.cp, St.id.ep)

def symC : Array (Array Nat) := #[#[0,1,2,3,4,5,6,7], #[3,2,1,0,7,6,5,4], #[4,5,6,7,0,1,2,3], #[7,6,5,4,3,2,1,0], #[1,0,3,2,5,4,7,6], #[2,3,0,1,6,7,4,5], #[5,4,7,6,1,0,3,2], #[6,7,4,5,2,3,0,1], #[0,3,2,1,4,7,6,5], #[3,0,1,2,7,4,5,6], #[4,7,6,5,0,3,2,1], #[7,4,5,6,3,0,1,2], #[1,2,3,0,5,6,7,4], #[2,1,0,3,6,5,4,7], #[5,6,7,4,1,2,3,0], #[6,5,4,7,2,1,0,3]]
def symCi : Array (Array Nat) := #[#[0,1,2,3,4,5,6,7], #[3,2,1,0,7,6,5,4], #[4,5,6,7,0,1,2,3], #[7,6,5,4,3,2,1,0], #[1,0,3,2,5,4,7,6], #[2,3,0,1,6,7,4,5], #[5,4,7,6,1,0,3,2], #[6,7,4,5,2,3,0,1], #[0,3,2,1,4,7,6,5], #[1,2,3,0,5,6,7,4], #[4,7,6,5,0,3,2,1], #[5,6,7,4,1,2,3,0], #[3,0,1,2,7,4,5,6], #[2,1,0,3,6,5,4,7], #[7,4,5,6,3,0,1,2], #[6,5,4,7,2,1,0,3]]
def symE : Array (Array Nat) := #[#[0,1,2,3,4,5,6,7,8,9,10,11], #[0,3,2,1,4,7,6,5,11,10,9,8], #[4,5,6,7,0,1,2,3,8,9,10,11], #[4,7,6,5,0,3,2,1,11,10,9,8], #[2,1,0,3,6,5,4,7,9,8,11,10], #[2,3,0,1,6,7,4,5,10,11,8,9], #[6,5,4,7,2,1,0,3,9,8,11,10], #[6,7,4,5,2,3,0,1,10,11,8,9], #[1,0,3,2,5,4,7,6,8,11,10,9], #[3,0,1,2,7,4,5,6,11,8,9,10], #[5,4,7,6,1,0,3,2,8,11,10,9], #[7,4,5,6,3,0,1,2,11,8,9,10], #[1,2,3,0,5,6,7,4,9,10,11,8], #[3,2,1,0,7,6,5,4,10,9,8,11], #[5,6,7,4,1,2,3,0,9,10,11,8], #[7,6,5,4,3,2,1,0,10,9,8,11]]
def symEi : Array (Array Nat) := #[#[0,1,2,3,4,5,6,7,8,9,10,11], #[0,3,2,1,4,7,6,5,11,10,9,8], #[4,5,6,7,0,1,2,3,8,9,10,11], #[4,7,6,5,0,3,2,1,11,10,9,8], #[2,1,0,3,6,5,4,7,9,8,11,10], #[2,3,0,1,6,7,4,5,10,11,8,9], #[6,5,4,7,2,1,0,3,9,8,11,10], #[6,7,4,5,2,3,0,1,10,11,8,9], #[1,0,3,2,5,4,7,6,8,11,10,9], #[1,2,3,0,5,6,7,4,9,10,11,8], #[5,4,7,6,1,0,3,2,8,11,10,9], #[5,6,7,4,1,2,3,0,9,10,11,8], #[3,0,1,2,7,4,5,6,11,8,9,10], #[3,2,1,0,7,6,5,4,10,9,8,11], #[7,4,5,6,3,0,1,2,11,8,9,10], #[7,6,5,4,3,2,1,0,10,9,8,11]]
def muArr : Array Nat := #[0,1,2,0,4,0,0,7,0,9,10,11,0,13,0,0,16,0,2,1,0,0,4,0,0,16,0,11,10,9,0,13,0,0,7,0,11,10,9,0,4,0,0,7,0,2,1,0,0,13,0,0,16,0,9,10,11,0,4,0,0,16,0,0,1,2,0,13,0,0,7,0,2,1,0,0,13,0,0,7,0,11,10,9,0,4,0,0,16,0,0,1,2,0,13,0,0,16,0,9,10,11,0,4,0,0,7,0,9,10,11,0,13,0,0,7,0,0,1,2,0,4,0,0,16,0,11,10,9,0,13,0,0,16,0,2,1,0,0,4,0,0,7,0,2,1,0,0,7,0,0,4,0,11,10,9,0,16,0,0,13,0,0,1,2,0,7,0,0,13,0,9,10,11,0,16,0,0,4,0,9,10,11,0,7,0,0,4,0,0,1,2,0,16,0,0,13,0,11,10,9,0,7,0,0,13,0,2,1,0,0,16,0,0,4,0,0,1,2,0,16,0,0,4,0,9,10,11,0,7,0,0,13,0,2,1,0,0,16,0,0,13,0,11,10,9,0,7,0,0,4,0,11,10,9,0,16,0,0,4,0,2,1,0,0,7,0,0,13,0,9,10,11,0,16,0,0,13,0,0,1,2,0,7,0,0,4,0]
def invS : Array Nat := #[0,1,2,3,4,5,6,7,8,12,10,14,9,13,11,15]

def conjA (σ σi a : Array Nat) (n : Nat) : Array Nat := (List.range n).toArray.map (fun i => σi[a[σ[i]!]!]!)
def conjC (s : Nat) (a : Array Nat) : Array Nat := conjA symC[s]! symCi[s]! a 8
def conjE (s : Nat) (a : Array Nat) : Array Nat := conjA symE[s]! symEi[s]! a 12
def conjP (s : Nat) (p : P) : P := (conjC s p.1, conjE s p.2)
def mu (s m : Nat) : Nat := muArr[s * 18 + m]!

def g2A : Array Nat := g2Moves.toArray
def cpG : HashMap (Array Nat) Unit := closure St.id.cp cpAct g2Moves
def epG : HashMap (Array Nat) Unit := closure St.id.ep epAct g2Moves
def cpGL : Array (Array Nat) := (cpG.toList.map Prod.fst).toArray
def epGL : Array (Array Nat) := (epG.toList.map Prod.fst).toArray
def cpGI : HashMap (Array Nat) Nat := mkIdx cpGL.toList
def epGI : HashMap (Array Nat) Nat := mkIdx epGL.toList

def NCP : Nat := 40320
def NE : Nat := 967680

def symTab : Array Nat × Array Nat × Array Nat := Id.run do
  let mut cls := Array.replicate NCP 99999
  let mut sy := Array.replicate NCP 0
  let mut reps : Array Nat := #[]
  for r in [0:NCP] do
    if cls[r]! == 99999 then
      let c := reps.size
      reps := reps.push r
      for s in [0:16] do
        let rq := cpGI[conjC s cpGL[r]!]!
        if cls[rq]! == 99999 then
          cls := cls.set! rq c
          sy := sy.set! rq invS[s]!
  return (cls, sy, reps)
def clsT : Array Nat := symTab.1
def syT : Array Nat := symTab.2.1
def repsT : Array Nat := symTab.2.2
def NC : Nat := 2768

def cpMv : Array Nat := Id.run do
  let mut t := Array.replicate (NCP * 10) 0
  for r in [0:NCP] do
    for j in [0:10] do
      t := t.set! (r * 10 + j) cpGI[cpAct cpGL[r]! g2A[j]!]!
  return t
def epMv : Array Nat := Id.run do
  let mut t := Array.replicate (NE * 10) 0
  for e in [0:NE] do
    for j in [0:10] do
      t := t.set! (e * 10 + j) epGI[epAct epGL[e]! g2A[j]!]!
  return t
def epCj : Array Nat := Id.run do
  let mut t := Array.replicate (NE * 16) 0
  for e in [0:NE] do
    for s in [0:16] do
      t := t.set! (e * 16 + s) epGI[conjE s epGL[e]!]!
  return t
def pcT : Array Nat := (List.range NC).toArray.map (fun c => inv cpGL[repsT[c]!]!.toList % 2)
def peT : Array Nat := (List.range NE).toArray.map (fun e => inv epGL[e]!.toList % 2)

/-- nonidentity symmetries fixing the class representative -/
def stabT : Array (List Nat) := (List.range NC).toArray.map (fun c =>
  (List.range 16).filter (fun t => t != 0 && conjC t cpGL[repsT[c]!]! == cpGL[repsT[c]!]!))
/-- canonical edge index within a class: least index over the stabilizer conjugates -/
@[inline] def canon (c e : Nat) : Nat := (stabT[c]!).foldl (fun a t => min a epCj[e * 16 + t]!) e

def N2 : Nat := NC * NE
def stateOf (i : Nat) : P := (cpGL[repsT[i / NE]!]!, epGL[i % NE]!)
def cellOf (p : P) : Nat :=
  let r := cpGI[p.1]!
  clsT[r]! * NE + canon clsT[r]! epGI[conjE syT[r]! p.2]!
def idCell : Nat := cellOf idP
@[inline] def nextC (i j : Nat) : Nat :=
  let r' := cpMv[repsT[i / NE]! * 10 + j]!
  clsT[r']! * NE + canon clsT[r']! epCj[epMv[(i % NE) * 10 + j]! * 16 + syT[r']!]!
@[inline] def parC (i : Nat) : Nat := (pcT[i / NE]! + peT[i % NE]!) % 2

def dist2F (_ : Unit) : ByteArray := Id.run do
  let mut d := ByteArray.emptyWithCapacity N2
  for _ in [0:N2] do d := d.push 255
  d := d.set! idCell 0
  for depth in [0:18] do
    let dv := depth.toUInt8
    for i in [0:N2] do
      if d.get! i == dv then
        for j in [0:10] do
          let k := nextC i j
          if d.get! k == 255 then d := d.set! k (dv + 1)
  return d

def anyMove2 (d : ByteArray) (i v : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => if (d.get! (nextC i j)).toNat + 1 == v && parC (nextC i j) == 0 then true else anyMove2 d i v j

def cell2Ok (d : ByteArray) (i : Nat) : Bool :=
  parC i != 0 || canon (i / NE) (i % NE) != i % NE ||
  (let v := (d.get! i).toNat
   decide (v ≤ 18) && (v != 0 || i == idCell) && (v == 0 || anyMove2 d i v 10))

def chk2From (d : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => if cell2Ok d n then chk2From d n else false

def k2CheckF2 (_ : Unit) : Bool := chk2From (dist2F ()) N2

def hist2F (_ : Unit) : List Nat := Id.run do
  let d := dist2F ()
  let mut h : Array Nat := Array.replicate 256 0
  for i in [0:N2] do
    let v := (d.get! i).toNat
    h := h.set! v (h[v]! + 1)
  return (h.toList.take 19) ++ [h[255]!]

def stats2 : List Nat := [cpGL.size, epGL.size, repsT.size, idCell, cpMv.size, epMv.size, epCj.size,
  (stabT.toList.filter (fun l => !l.isEmpty)).length, (stabT.toList.map List.length).foldl (· + ·) 0]

def diag2F (_ : Unit) : List Nat × Bool := Id.run do
  let d := dist2F ()
  let mut h : Array Nat := Array.replicate 256 0
  for i in [0:N2] do
    let v := (d.get! i).toNat
    h := h.set! v (h[v]! + 1)
  return ((h.toList.take 19) ++ [h[255]!], chk2From d N2)
