import Cube.Phase12
import Cube.Square
import Cube.Parity
open Std
set_option compiler.extract_closed false

def clsM (e : Nat) : Nat := if e = 1 ∨ e = 3 ∨ e = 5 ∨ e = 7 then 1 else 0
def maskMSof (ep : Array Nat) : Array Nat := ep.map clsM
def cpAct (c : Array Nat) (m : Nat) : Array Nat := (List.range 8).toArray.map (fun i => c[(moves[m]!).cp[i]!]!)

/-- G2 = <U, D, R2, L2, F2, B2> -/
def g2Moves : List Nat := [0, 1, 2, 9, 10, 11, 4, 13, 7, 16]

def closure {K : Type} [BEq K] [Hashable K] [Inhabited K] (start : K) (act : K → Nat → K) (gens : List Nat) : HashMap K Unit := Id.run do
  let mut seen : HashMap K Unit := HashMap.emptyWithCapacity 50000
  seen := seen.insert start ()
  let mut stack : Array K := #[start]
  while stack.size > 0 do
    let x := stack.back!
    stack := stack.pop
    for m in gens do
      let y := act x m
      if !seen.contains y then
        seen := seen.insert y (); stack := stack.push y
  return seen

def cpSet : HashMap (Array Nat) Unit := closure St.id.cp cpAct allMoves
def cpClosed : Bool := cpSet.toList.all (fun p => allMoves.all (fun m => cpSet.contains (cpAct p.1 m)))

abbrev PK := Array Nat × Array Nat
def pkAct (k : PK) (m : Nat) : PK := (maskAct k.1 m, maskAct k.2 m)
def idE : Array Nat := maskOf St.id.ep
def idMS : Array Nat := maskMSof St.id.ep
def pairSet : HashMap PK Unit := closure (idE, idMS) pkAct allMoves
def pairClosed : Bool := pairSet.toList.all (fun p => allMoves.all (fun m => pairSet.contains (pkAct p.1 m)))
def ms70 : List (Array Nat) := (pairSet.toList.filter (fun p => p.1.1 == idE)).map (fun p => p.1.2)

def hSet : HashMap (Array Nat) Unit := closure St.id.cp cpAct half
def hList : List (Array Nat) := hSet.toList.map Prod.fst

abbrev K3 := Array Nat × Array Nat
def k3Act (k : K3) (m : Nat) : K3 := (cpAct k.1 m, maskAct k.2 m)
def k3ActList (k : K3) (w : List Nat) : K3 := w.foldl k3Act k
def k3Target (k : K3) : Bool := hSet.contains k.1 && k.2 == idMS
def k3TableF (_ : Unit) : HashMap K3 (Option (List Nat)) := solveTable (St.id.cp, idMS) k3Act g2Moves g2Moves k3Target 13

def k3OkW (t : HashMap K3 (Option (List Nat))) (cp k : Array Nat) : Bool :=
  match t[(cp, k)]? with
  | some (some w) => decide (w.length ≤ 13) && w.all (fun m => g2Moves.contains m) && k3Target (k3ActList (cp, k) w)
  | _ => false
def k3CheckW (t : HashMap K3 (Option (List Nat))) : Bool := cpSet.toList.all (fun p => ms70.all (fun k => k3OkW t p.1 k))
def k3CheckF (_ : Unit) : Bool := k3CheckW (k3TableF ())

def g2Keep : Bool := g2Moves.all (fun m => g1Moves.contains m && decide (coAct St.id.co m = St.id.co) && decide (maskAct idE m = idE))
def hEven : Bool := hList.all (fun c => decide (inv c.toList % 2 = 0))

def stats34 (_ : Unit) : List Nat := let k3Table := k3TableF (); [cpSet.size, pairSet.size, ms70.length, hSet.size, k3Table.size,
  k3Table.fold (fun a _ o => max a ((o.map List.length).getD 99)) 0]
