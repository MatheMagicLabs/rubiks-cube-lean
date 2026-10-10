import CubeH.Kph2
open Std
set_option compiler.extract_closed false

/-! Lower bound 18 for Kociemba's phase 2: the certified phase-2 table is 1-Lipschitz along the ten phase-2 moves,
and cells are invariant under conjugation by the 16 symmetries (finite facts below). -/

/-- composition of symmetries: `conj a ∘ conj b = conj (smul a b)` -/
def symMulT : Array Nat := (List.range 256).toArray.map (fun ab =>
  let a := ab / 16
  let b := ab % 16
  ((List.range 16).find? (fun c => (List.range 8).all (fun i => symC[c]![i]! == symC[b]![symC[a]![i]!]!) &&
     (List.range 12).all (fun i => symE[c]![i]! == symE[b]![symE[a]![i]!]!))).getD 99)
def smul (a b : Nat) : Nat := symMulT[a * 16 + b]!

def low2FactsF (_ : Unit) : Bool :=
  (List.range 16).all (fun a => (List.range 16).all (fun b => decide (smul a b < 16))) &&
  cpG.toList.all (fun p => (List.range 16).all (fun a => (List.range 16).all (fun b =>
    conjC a (conjC b p.1) == conjC (smul a b) p.1))) &&
  epG.toList.all (fun p => (List.range 16).all (fun a => (List.range 16).all (fun b =>
    conjE a (conjE b p.1) == conjE (smul a b) p.1))) &&
  (List.range NCP).all (fun r => cpGI[cpGL[r]!]! == r) &&
  (List.range NE).all (fun e => epGI[epGL[e]!]! == e && epCj[e * 16]! == e) &&
  (List.range NC).all (fun c => clsT[repsT[c]!]! == c &&
     (List.range 16).all (fun u => clsT[cpGI[conjC u cpGL[repsT[c]!]!]!]! == c &&
        (conjC u cpGL[repsT[c]!]! != cpGL[repsT[c]!]! || u == 0 || (stabT[c]!).contains u)))

def canonInvF (_ : Unit) : Bool := (List.range NC).all (fun c => (stabT[c]!).isEmpty ||
  (List.range NE).all (fun e => (stabT[c]!).all (fun u => canon c epCj[e * 16 + u]! == canon c e)))

def lipCell2 (d : ByteArray) (i : Nat) : Bool :=
  canon (i / NE) (i % NE) != i % NE ||
  (List.range 10).all (fun j => decide ((d.get! i).toNat ≤ (d.get! (nextC i j)).toNat + 1))
def lip2From (d : ByteArray) : Nat → Bool
  | 0 => true
  | n + 1 => if lipCell2 d n then lip2From d n else false

/-- the "mirror" element: the permutation induced by the R–L reflection on all U/D pieces -/
def mirrorP : P := (#[1,0,3,2,5,4,7,6], #[2,1,0,3,6,5,4,7,8,9,10,11])

def low2F (_ : Unit) : Bool :=
  let d := dist2F ()
  lip2From d N2 && (d.get! idCell).toNat == 0 && cpG.contains mirrorP.1 && epG.contains mirrorP.2 &&
    (d.get! (cellOf mirrorP)).toNat == 18
