import Cube.Model
import Std.Data.HashMap
open Std
set_option compiler.extract_closed false

/-! Coordinates for Thistlethwaite phases 1 (EO) and 2 (CO + E-slice), with move actions that are
definitionally (phase 1) or provably (phase 2) the projections of `apply`. -/

def eoAct (e : Array Nat) (m : Nat) : Array Nat :=
  (List.range 12).toArray.map (fun i => (e[(moves[m]!).ep[i]!]! + (moves[m]!).eo[i]!) % 2)
def coAct (c : Array Nat) (m : Nat) : Array Nat :=
  (List.range 8).toArray.map (fun i => (c[(moves[m]!).cp[i]!]! + (moves[m]!).co[i]!) % 3)
def cls (e : Nat) : Nat := if e ≥ 8 then 1 else 0
def maskOf (ep : Array Nat) : Array Nat := ep.map cls
def maskAct (k : Array Nat) (m : Nat) : Array Nat :=
  (List.range 12).toArray.map (fun i => k[(moves[m]!).ep[i]!]!)

def allMoves : List Nat := List.range 18
/-- G1 = <U, D, R, L, F2, B2> -/
def g1Moves : List Nat := [0, 1, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 14, 16]

/-- generic: closure of `start` under `act` with all `gens`, then solving words (using `solveGens`) to `target`
by repeated backward sweeps; entries without a solving word get none. -/
def solveTable {K : Type} [BEq K] [Hashable K] [Inhabited K] (start : K) (act : K → Nat → K) (gens solveGens : List Nat)
    (target : K → Bool) (maxd : Nat) : HashMap K (Option (List Nat)) := Id.run do
  -- closure
  let mut seen : HashMap K Unit := HashMap.emptyWithCapacity 1100000
  seen := seen.insert start ()
  let mut stack : Array K := #[start]
  let mut all : Array K := #[start]
  while stack.size > 0 do
    let x := stack.back!
    stack := stack.pop
    for m in gens do
      let y := act x m
      if !seen.contains y then
        seen := seen.insert y (); stack := stack.push y; all := all.push y
  -- solving words
  let mut sol : HashMap K (Option (List Nat)) := HashMap.emptyWithCapacity 1100000
  for x in all do
    sol := sol.insert x (if target x then some [] else none)
  for _ in [0:maxd] do
    let mut upd : Array (K × List Nat) := #[]
    for x in all do
      if (sol.getD x none).isNone then
        let mut best : Option (List Nat) := none
        for m in solveGens do
          if best.isNone then
            match sol.getD (act x m) none with
            | some w => best := some (m :: w)
            | none => pure ()
        if let some w := best then upd := upd.push (x, w)
    for (x, w) in upd do sol := sol.insert x (some w)
  return sol

def eoZero : Array Nat := St.id.eo
def eoTable : HashMap (Array Nat) (Option (List Nat)) :=
  solveTable eoZero eoAct allMoves allMoves (fun e => e == eoZero) 7

def eoActList (e : Array Nat) (w : List Nat) : Array Nat := w.foldl eoAct e

def eoEntryOk (e : Array Nat) (o : Option (List Nat)) : Bool :=
  match o with
  | none => false
  | some w => decide (w.length ≤ 7) && w.all (fun m => decide (m < 18)) && decide (eoActList e w = eoZero) &&
      allMoves.all (fun m => eoTable.contains (eoAct e m))
def eoCheck : Bool := eoTable.toList.all (fun p => eoEntryOk p.1 p.2) && eoTable.contains eoZero

-- phase 2 coordinate: (co, E-slice mask)
abbrev K2 := Array Nat × Array Nat
def k2Act (k : K2) (m : Nat) : K2 := (coAct k.1 m, maskAct k.2 m)
def k2Start : K2 := (St.id.co, maskOf St.id.ep)
def k2TableF (_ : Unit) : HashMap K2 (Option (List Nat)) :=
  solveTable k2Start k2Act allMoves g1Moves (fun k => k == k2Start) 10
def k2ActList (k : K2) (w : List Nat) : K2 := w.foldl k2Act k
def k2EntryOkW (t : HashMap K2 (Option (List Nat))) (k : K2) (o : Option (List Nat)) : Bool :=
  match o with
  | none => false
  | some w => decide (w.length ≤ 10) && w.all (fun m => g1Moves.contains m) && decide (k2ActList k w = k2Start) &&
      allMoves.all (fun m => t.contains (k2Act k m))
def k2CheckW (t : HashMap K2 (Option (List Nat))) : Bool := t.toList.all (fun p => k2EntryOkW t p.1 p.2) && t.contains k2Start
def k2CheckF (_ : Unit) : Bool := k2CheckW (k2TableF ())
def g1KeepsEO : Bool := g1Moves.all (fun m => decide (eoAct eoZero m = eoZero))

def stats (_ : Unit) : List Nat := let k2Table := k2TableF (); [eoTable.size, k2Table.size,
  eoTable.fold (fun a _ o => max a ((o.map List.length).getD 99)) 0,
  k2Table.fold (fun a _ o => max a ((o.map List.length).getD 99)) 0]
