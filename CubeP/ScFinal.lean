import CubeP.ScProof
open Std

/-! **Supercube: God's number (half-turn metric) is at least 22.** The supercube position "superflip, every centre
at home" exists (an explicit 254-move word reaches it) and no word of fewer than 22 face turns reaches it. -/

/-- 20-move superflip, then (D B)^105 and two 180° centre twists (R U D R2 U' D')^2, (L U D L2 U' D')^2 that restore
the centres. -/
def scWitness : List Nat := [0,4,6,15,3,16,3,1,12,16,3,2,11,4,6,5,12,16,1,7,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,9,15,3,0,9,4,2,11,3,0,9,4,2,11,12,0,9,13,2,11,12,0,9,13,2,11]

theorem sc_witness_facts : (∀ m ∈ scWitness, m < 18) ∧ eval scWitness = sfSt ∧ sigOf scWitness = sig0 := by
  native_decide

theorem supercube_gods_number_ge_22 : ∃ w : List Nat, (∀ m ∈ w, m < 18) ∧ eval w = sfSt ∧ sigOf w = sig0 ∧
    ∀ v : List Nat, (∀ m ∈ v, m < 18) → eval v = eval w → sigOf v = sigOf w → 22 ≤ v.length :=
  ⟨scWitness, sc_witness_facts.1, sc_witness_facts.2.1, sc_witness_facts.2.2, fun v hv h1 h2 =>
    supercube_superflip v hv (h1.trans sc_witness_facts.2.1) (h2.trans sc_witness_facts.2.2)⟩

#print axioms supercube_gods_number_ge_22
