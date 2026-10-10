import Cube.Kph1
import CubeH.Kph2
open Std
set_option compiler.extract_closed false

/-! Certificate search for the superflip lower bound (20 face turns).

A shortest solution of the superflip can be rotated cyclically and conjugated by whole-cube rotations (the superflip
is central and symmetric). Normalised, it reads `s1 ++ s2` where `s2` is a run of ⟨U,D,R2,L2,F2,B2⟩-moves at least as
long as every run of H-moves (for any of the three axes) inside `s1`, `s1` starts with R or R' and ends with a move
outside H. The search enumerates all such `s1` with
* the Kociemba phase-1 table on three axes as lower bounds (the URF rotation `muS` changes the axis),
* the run bound `|s2| ≥ maxRun s1`,
* and, where `s1` ends in H, the exact phase-2 distance as lower bound for `s2`. -/

/-- the superflip -/
def sfSt : St := ⟨St.id.cp, St.id.co, St.id.ep, #[1,1,1,1,1,1,1,1,1,1,1,1]⟩

/-- conjugation of moves by the URF rotation (U → F, R → U, F → R, D → B, L → D, B → L) -/
def muSArr : Array Nat := #[6,7,8,0,1,2,3,4,5,15,16,17,9,10,11,12,13,14]
def muS (m : Nat) : Nat := muSArr[m]!

def isHUD (m : Nat) : Bool := g2Moves.contains m
/-- move `m` lies in the phase-2 group of axis `a` -/
def isHa (a m : Nat) : Bool := if a = 0 then isHUD m else if a = 1 then isHUD (muS m) else isHUD (muS (muS m))

/-- current H-runs on the three axes and the longest run so far -/
structure RunSt where
  r0 : Nat
  r1 : Nat
  r2 : Nat
  mx : Nat
deriving Inhabited

def runStep (s : RunSt) (m : Nat) : RunSt :=
  let a := if isHa 0 m then s.r0 + 1 else 0
  let b := if isHa 1 m then s.r1 + 1 else 0
  let c := if isHa 2 m then s.r2 + 1 else 0
  ⟨a, b, c, max s.mx (max a (max b c))⟩

def run0 : RunSt := ⟨0, 0, 0, 0⟩
def runOf (w : List Nat) : RunSt := w.foldl runStep run0

def allLt (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => if f n then allLt f n else false

def sfSearch (d1 d2 : ByteArray) : Nat → Nat → Nat → Nat → P → Nat → Nat → RunSt → Bool → Bool
  | fuel, r0, r1, r2, p, g, lastf, rs, lnh =>
    (!(lnh && (d1.get! r0).toNat == 0) || decide (20 ≤ g + max rs.mx (d2.get! (cellOf p)).toNat)) &&
    (match fuel with
     | 0 => true
     | f + 1 => allLt (fun m =>
         m / 3 == lastf || (g == 0 && !(m == 3 || m == 5)) ||
         (let s0 := next r0 m
          let s1 := next r1 (muS m)
          let s2 := next r2 (muS (muS m))
          let rs' := runStep rs m
          decide (19 < g + 1 + (d1.get! s0).toNat + rs'.mx) || decide (19 < g + 1 + (d1.get! s1).toNat) ||
            decide (19 < g + 1 + (d1.get! s2).toNat) ||
            sfSearch d1 d2 f s0 s1 s2 (pAct p m) (g + 1) (m / 3) rs' (!isHUD m))) 18)

def sfF (_ : Unit) : Bool :=
  let d1 := distF ()
  let d2 := dist2F ()
  let r := rank sfSt
  sfSearch d1 d2 19 r r r idP 0 6 run0 false
