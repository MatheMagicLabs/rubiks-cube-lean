import CubeG.Gods
open Std
set_option compiler.extract_closed false

/-! Slice and anti-slice groups. A pair move turns both outer layers of one axis at once:
`pairMoves anti g` with `g = 3*axis + k` (axis 0 = R/L, 1 = U/D, 2 = F/B; `k+1` = power of the first face).
Slice move: R^p L^-p (both layers turn the same way in space, i.e. a middle-slice turn up to a rotation);
anti-slice move: R^p L^p. -/
def axisFaces : List (Nat × Nat) := [(1, 4), (0, 3), (2, 5)]
def pairMoves (anti : Bool) (g : Nat) : List Nat :=
  let ab := axisFaces[g / 3]!
  let k := g % 3
  [3 * ab.1 + k, 3 * ab.2 + (if anti then k else 2 - k)]
def pairAct (anti : Bool) (x : St) (g : Nat) : St := applyList x (pairMoves anti g)
/-- quarter pair moves only, and quarter + half pair moves -/
def pairQ : List Nat := [0, 2, 3, 5, 6, 8]
def pairH : List Nat := List.range 9

def sliceQF (_ : Unit) : Bool := godCheck (godTable St.id (pairAct false) pairQ) St.id (pairAct false) pairQ 6
def sliceHF (_ : Unit) : Bool := godCheck (godTable St.id (pairAct false) pairH) St.id (pairAct false) pairH 5
def antiQF (_ : Unit) : Bool := godCheck (godTable St.id (pairAct true) pairQ) St.id (pairAct true) pairQ 9
def antiHF (_ : Unit) : Bool := godCheck (godTable St.id (pairAct true) pairH) St.id (pairAct true) pairH 8
def sliceStatsF (_ : Unit) : List (List Nat) :=
  let a := godTable St.id (pairAct false) pairQ
  let b := godTable St.id (pairAct false) pairH
  let c := godTable St.id (pairAct true) pairQ
  let d := godTable St.id (pairAct true) pairH
  [[a.size, b.size, c.size, d.size], godHist a, godHist b, godHist c, godHist d]
