/-! Cubie model of the 3x3x3 (Kociemba's conventions).
Corners: URF UFL ULB UBR DFR DLF DBL DRB; edges: UR UF UL UB DR DF DL DB FR FL BL BR.
A state is (cp, co, ep, eo); `mul s m` applies move m after s:
  cp[i] = s.cp[m.cp[i]], co[i] = s.co[m.cp[i]] + m.co[i] (mod 3), likewise for edges (mod 2). -/

structure St where
  cp : Array Nat
  co : Array Nat
  ep : Array Nat
  eo : Array Nat
deriving Hashable, Repr, DecidableEq, Inhabited

def St.id : St := ⟨#[0,1,2,3,4,5,6,7], #[0,0,0,0,0,0,0,0], #[0,1,2,3,4,5,6,7,8,9,10,11], #[0,0,0,0,0,0,0,0,0,0,0,0]⟩

def St.mul (s m : St) : St :=
  ⟨(List.range 8).toArray.map (fun i => s.cp[m.cp[i]!]!),
   (List.range 8).toArray.map (fun i => (s.co[m.cp[i]!]! + m.co[i]!) % 3),
   (List.range 12).toArray.map (fun i => s.ep[m.ep[i]!]!),
   (List.range 12).toArray.map (fun i => (s.eo[m.ep[i]!]! + m.eo[i]!) % 2)⟩

-- basic clockwise quarter turns U R F D L B
def bU : St := ⟨#[3,0,1,2,4,5,6,7], #[0,0,0,0,0,0,0,0], #[3,0,1,2,4,5,6,7,8,9,10,11], #[0,0,0,0,0,0,0,0,0,0,0,0]⟩
def bR : St := ⟨#[4,1,2,0,7,5,6,3], #[2,0,0,1,1,0,0,2], #[8,1,2,3,11,5,6,7,4,9,10,0], #[0,0,0,0,0,0,0,0,0,0,0,0]⟩
def bF : St := ⟨#[1,5,2,3,0,4,6,7], #[1,2,0,0,2,1,0,0], #[0,9,2,3,4,8,6,7,1,5,10,11], #[0,1,0,0,0,1,0,0,1,1,0,0]⟩
def bD : St := ⟨#[0,1,2,3,5,6,7,4], #[0,0,0,0,0,0,0,0], #[0,1,2,3,5,6,7,4,8,9,10,11], #[0,0,0,0,0,0,0,0,0,0,0,0]⟩
def bL : St := ⟨#[0,2,6,3,4,1,5,7], #[0,1,2,0,0,2,1,0], #[0,1,10,3,4,5,9,7,8,2,6,11], #[0,0,0,0,0,0,0,0,0,0,0,0]⟩
def bB : St := ⟨#[0,1,3,7,4,5,2,6], #[0,0,1,2,0,0,2,1], #[0,1,2,11,4,5,6,10,8,9,3,7], #[0,0,0,1,0,0,0,1,0,0,1,1]⟩

def basic : Array St := #[bU, bR, bF, bD, bL, bB]

/-- move index 0..17: face = i / 3 (U R F D L B), power = i % 3 + 1 quarter turns -/
def moveSt (i : Nat) : St :=
  let b := basic[i / 3]!
  match i % 3 with
  | 0 => b
  | 1 => b.mul b
  | _ => (b.mul b).mul b

def moves : Array St := (List.range 18).toArray.map moveSt

def apply (s : St) (i : Nat) : St := s.mul moves[i]!
def applyList (s : St) (w : List Nat) : St := w.foldl apply s
def eval (w : List Nat) : St := applyList St.id w

def moveName (i : Nat) : String :=
  #["U","R","F","D","L","B"][i / 3]! ++ #["", "2", "'"][i % 3]!

def parseMove (t : String) : Option Nat := do
  let f ← ["U","R","F","D","L","B"].idxOf? (t.take 1)
  let p ← ["", "2", "'"].idxOf? (t.drop 1)
  pure (3 * f + p)

def parseAlg (s : String) : List Nat := (s.splitOn " ").filterMap (fun t => if t == "" then none else parseMove t)
