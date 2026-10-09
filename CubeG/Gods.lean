import Cube.Phase34
open Std
set_option compiler.extract_closed false

/-! Generic God's-number tables: BFS with a shortest word per element, plus a certificate check that gives both the
upper bound (every element has a word of length ≤ bound) and the lower bound (an element at table distance = bound
has no shorter word). Instantiated for the 2×2×2 cube (DBL corner fixed, moves U, R, F) in HTM and QTM. -/

def actList {K : Type} (act : K → Nat → K) (x : K) (w : List Nat) : K := w.foldl act x

def godTable {K : Type} [DecidableEq K] [Hashable K] (start : K) (act : K → Nat → K) (gens : List Nat) :
    HashMap K (List Nat) := Id.run do
  let mut tbl : HashMap K (List Nat) := HashMap.emptyWithCapacity 4000000
  tbl := tbl.insert start []
  let mut frontier : Array (K × List Nat) := #[(start, [])]
  while frontier.size > 0 do
    let mut nxt : Array (K × List Nat) := #[]
    for (x, w) in frontier do
      for h in gens do
        let y := act x h
        if !tbl.contains y then
          let wy := w ++ [h]
          tbl := tbl.insert y wy
          nxt := nxt.push (y, wy)
    frontier := nxt
  return tbl

def godEntryOk {K : Type} [DecidableEq K] [Hashable K] (t : HashMap K (List Nat)) (start : K) (act : K → Nat → K)
    (gens : List Nat) (bound : Nat) (x : K) (w : List Nat) : Bool :=
  w.all (fun m => gens.contains m) && decide (w.length ≤ bound) && decide (actList act start w = x) &&
  gens.all (fun h => match t[act x h]? with
    | some v => decide (v.length ≤ w.length + 1)
    | none => false)

def godCheck {K : Type} [DecidableEq K] [Hashable K] (t : HashMap K (List Nat)) (start : K) (act : K → Nat → K)
    (gens : List Nat) (bound : Nat) : Bool :=
  t.toList.all (fun p => godEntryOk t start act gens bound p.1 p.2) && decide (t[start]? = some []) &&
  t.toList.any (fun p => p.2.length == bound)

def godHist {K : Type} [DecidableEq K] [Hashable K] (t : HashMap K (List Nat)) : List Nat :=
  let a := t.fold (fun (a : Array Nat) _ w => a.modify w.length (· + 1)) (Array.replicate 30 0)
  a.toList.reverse.dropWhile (· == 0) |>.reverse

abbrev C2 := Array Nat × Array Nat
def c2Act (k : C2) (m : Nat) : C2 := (cpAct k.1 m, coAct k.2 m)
def c2Start : C2 := (St.id.cp, St.id.co)
def htm2 : List Nat := List.range 9
def qtm2 : List Nat := [0, 2, 3, 5, 6, 8]

def c2HtmCheckF (_ : Unit) : Bool := godCheck (godTable c2Start c2Act htm2) c2Start c2Act htm2 11
def c2QtmCheckF (_ : Unit) : Bool := godCheck (godTable c2Start c2Act qtm2) c2Start c2Act qtm2 14
def c2StatsF (_ : Unit) : List (List Nat) :=
  let a := godTable c2Start c2Act htm2
  let b := godTable c2Start c2Act qtm2
  [[a.size, b.size], godHist a, godHist b]
