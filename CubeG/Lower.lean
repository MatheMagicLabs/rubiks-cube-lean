import Cube.Kph1
open Std
set_option compiler.extract_closed false

/-! Lower bounds from the certified K1 distance table: the table is 1-Lipschitz along all 18 moves, so the stored
distance is a lower bound for reaching <U,D,R2,L2,F2,B2>-form. -/

def lipCell (d : ByteArray) (i : Nat) : Bool :=
  (List.range 18).all (fun m => decide ((d.get! i).toNat ≤ (d.get! (next i m)).toNat + 1))

def lipFrom (d : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => if lipCell d n then lipFrom d n else false

/-- the superflip, 20 face turns (Reid 1995) -/
def superflip : List Nat := parseAlg "U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2"

/-- a position at K1 distance 12 (found from the table: first cell at distance 12, solved and inverted) -/
def k1Witness : List Nat :=
  parseAlg "L2 D2 B2 R2 D2 B2 R2 D2 R2 U2 D' B2 U' F2 U' L2 U R2 U2 B' R' F2 U2 F L2 R' D U2 L' R' U'"
def k1WitnessValid : Bool := k1Witness.all (fun m => decide (m < 18))

def k1LowF (_ : Unit) : Bool :=
  let d := distF ()
  lipFrom d NN && (d.get! i0).toNat == 0 && (d.get! (rank (eval k1Witness))).toNat == 12
