import Cube.Model
import Std.Data.HashMap
open Std

/-! The square group G3 = <U2,R2,F2,D2,L2,B2>: BFS table with a shortest word for every element. -/

def half : List Nat := [1, 4, 7, 10, 13, 16]

def sqBfs : HashMap St (List Nat) := Id.run do
  let mut tbl : HashMap St (List Nat) := HashMap.emptyWithCapacity 700000
  tbl := tbl.insert St.id []
  let mut frontier : Array (St × List Nat) := #[(St.id, [])]
  while frontier.size > 0 do
    let mut next : Array (St × List Nat) := #[]
    for (x, w) in frontier do
      for h in half do
        let y := apply x h
        if !tbl.contains y then
          let wy := w ++ [h]
          tbl := tbl.insert y wy
          next := next.push (y, wy)
    frontier := next
  return tbl

def sqTable : HashMap St (List Nat) := sqBfs

/-- every entry: word uses half turns only, has length <= 15, evaluates to its key; the table is closed under
half turns, and the stored length is 1-Lipschitz along half turns (gives the lower bound). -/
def sqEntryOk (x : St) (w : List Nat) : Bool :=
  w.all (fun m => half.contains m) && decide (w.length ≤ 15) && decide (applyList St.id w = x) &&
  half.all (fun h => match sqTable[apply x h]? with
    | some v => decide (v.length ≤ w.length + 1)
    | none => false)

def sqCheck : Bool := sqTable.toList.all (fun p => sqEntryOk p.1 p.2) && decide (sqTable[St.id]? = some [])

def sqSize : Nat := sqTable.size
def sqMax : Nat := sqTable.fold (fun acc _ w => max acc w.length) 0
def sqFar : List (St × List Nat) := (sqTable.toList.filter (fun p => p.2.length == 15)).take 1
