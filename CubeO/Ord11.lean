import Cube.Kph1
open Std
set_option compiler.extract_closed false

/-! Elements of order 11. An element of order 11 has all corners solved (8 < 11 and 3 ∤ 11), so a corner distance
table gives pruning for an exhaustive search: no word of at most 9 face turns produces an element of order 11. -/

/-- corner permutations: index and move table over all 18 moves -/
def cpL : List (Array Nat) := cpSet.toList.map Prod.fst
def cpIdx : HashMap (Array Nat) Nat := mkIdx cpL
def TP : Array Nat := mkTab cpL cpIdx cpAct

def NCR : Nat := 40320 * 2187
def crank (x : St) : Nat := cpIdx[x.cp]! * 2187 + cIdx[x.co]!
@[inline] def cnext (i m : Nat) : Nat := TP[(i / 2187) * 18 + m]! * 2187 + TC[(i % 2187) * 18 + m]!
def c0 : Nat := cpIdx[St.id.cp]! * 2187 + cIdx[St.id.co]!

/-- BFS over corner states (permutation × orientation), all 18 moves; God's number of the corners is 11. -/
def cdistF (_ : Unit) : ByteArray := Id.run do
  let mut d := ByteArray.emptyWithCapacity NCR
  for _ in [0:NCR] do d := d.push 255
  d := d.set! c0 0
  for depth in [0:11] do
    let dv := depth.toUInt8
    for i in [0:NCR] do
      if d.get! i == dv then
        for m in [0:18] do
          let j := cnext i m
          if d.get! j == 255 then d := d.set! j (dv + 1)
  return d

def clipCell (d : ByteArray) (i : Nat) : Bool :=
  (List.range 18).all (fun m => decide ((d.get! i).toNat ≤ (d.get! (cnext i m)).toNat + 1))
def clipFrom (d : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => if clipCell d n then clipFrom d n else false

/-- powers -/
def stPow (x : St) : Nat → St
  | 0 => St.id
  | n + 1 => let q := stPow x n; q.mul x
def permPow (p : Array Nat) : Nat → Array Nat
  | 0 => St.id.cp
  | n + 1 => let q := permPow p n; (List.range 8).toArray.map (fun i => q[p[i]!]!)
def coPow (c : Array Nat) : Nat → Array Nat
  | 0 => St.id.co
  | n + 1 => let q := coPow c n; (List.range 8).toArray.map (fun i => (q[St.id.cp[i]!]! + c[i]!) % 3)

def isOrd11 (x : St) : Bool := x != St.id && stPow x 11 == St.id
def cSolved (x : St) : Bool := x.cp == St.id.cp && x.co == St.id.co

/-- finite facts: corner permutation index table, and `p^11 = 1 → p = 1` for corner permutations,
`c^11 = 0 → c = 0` for corner orientations with solved permutation -/
def ordCompF (_ : Unit) : Bool := cpClosed && cpSet.contains St.id.cp && tabOk cpL cpIdx cpAct TP 40320 St.id.cp &&
  cpL.all (fun p => permPow p 11 != St.id.cp || p == St.id.cp) &&
  coL.all (fun c => coPow c 11 != St.id.co || c == St.id.co)

/-- exhaustive search with corner pruning (all words, no canonical-sequence reduction); `i` tracks the corner
rank of `x`, so pruned children are never built -/
def dfs11 (d : ByteArray) (x : St) (i : Nat) : Nat → Bool
  | 0 => !(cSolved x && isOrd11 x)
  | n + 1 => !(cSolved x && isOrd11 x) &&
      (List.range 18).all (fun m => decide (n < (d.get! (cnext i m)).toNat) || dfs11 d (apply x m) (cnext i m) n)

def ord11F (_ : Unit) : Bool :=
  let d := cdistF ()
  clipFrom d NCR && (d.get! c0).toNat == 0 && dfs11 d St.id (crank St.id) 9

/-- a 10-move word of order 11: corners solved, edges in one 11-cycle -/
def ord11Word : List Nat := parseAlg "U R U F R' L U' R' F' D'"
def ord11WitF (_ : Unit) : Bool := ord11Word.length == 10 && ord11Word.all (fun m => decide (m < 18)) &&
  isOrd11 (eval ord11Word)

def cHistF (_ : Unit) : List Nat := Id.run do
  let d := cdistF ()
  let mut h : Array Nat := Array.replicate 256 0
  for i in [0:NCR] do
    let v := (d.get! i).toNat
    h := h.set! v (h[v]! + 1)
  return (h.toList.take 12) ++ [h[255]!]
