import CubeP.SliceThm
import CubeP.GodsProof

/-- a word of pair moves is the face-turn word obtained by expanding each pair -/
theorem pairAct_list (anti : Bool) (x : St) (w : List Nat) :
    actList (pairAct anti) x w = applyList x (w.flatMap (pairMoves anti)) := by
  induction w generalizing x with
  | nil => simp only [actList, applyList, List.flatMap_nil, List.foldl_nil]
  | cons g w ih =>
    rw [actList_cons, ih]
    simp only [pairAct, List.flatMap_cons, applyList, List.foldl_append]

/-- God's number of the slice group ⟨RL⁻¹, UD⁻¹, FB⁻¹⟩ (768 elements) with quarter slice moves is 6. -/
theorem slice_group_quarter :
    (∀ w, (∀ m ∈ w, m ∈ pairQ) → ∃ w', (∀ m ∈ w', m ∈ pairQ) ∧ w'.length ≤ 6 ∧
        actList (pairAct false) St.id w' = actList (pairAct false) St.id w) ∧
    (∃ w0, (∀ m ∈ w0, m ∈ pairQ) ∧ ∀ w, (∀ m ∈ w, m ∈ pairQ) →
        actList (pairAct false) St.id w = actList (pairAct false) St.id w0 → 6 ≤ w.length) :=
  god_number (by have := sliceQ_true; unfold sliceQF at this; exact this)

/-- ... with quarter and half slice moves it is 5. -/
theorem slice_group_half :
    (∀ w, (∀ m ∈ w, m ∈ pairH) → ∃ w', (∀ m ∈ w', m ∈ pairH) ∧ w'.length ≤ 5 ∧
        actList (pairAct false) St.id w' = actList (pairAct false) St.id w) ∧
    (∃ w0, (∀ m ∈ w0, m ∈ pairH) ∧ ∀ w, (∀ m ∈ w, m ∈ pairH) →
        actList (pairAct false) St.id w = actList (pairAct false) St.id w0 → 5 ≤ w.length) :=
  god_number (by have := sliceH_true; unfold sliceHF at this; exact this)

/-- God's number of the anti-slice group ⟨RL, UD, FB⟩ (6144 elements) with quarter anti-slice moves is 9. -/
theorem antislice_group_quarter :
    (∀ w, (∀ m ∈ w, m ∈ pairQ) → ∃ w', (∀ m ∈ w', m ∈ pairQ) ∧ w'.length ≤ 9 ∧
        actList (pairAct true) St.id w' = actList (pairAct true) St.id w) ∧
    (∃ w0, (∀ m ∈ w0, m ∈ pairQ) ∧ ∀ w, (∀ m ∈ w, m ∈ pairQ) →
        actList (pairAct true) St.id w = actList (pairAct true) St.id w0 → 9 ≤ w.length) :=
  god_number (by have := antiQ_true; unfold antiQF at this; exact this)

/-- ... with quarter and half anti-slice moves it is 8. -/
theorem antislice_group_half :
    (∀ w, (∀ m ∈ w, m ∈ pairH) → ∃ w', (∀ m ∈ w', m ∈ pairH) ∧ w'.length ≤ 8 ∧
        actList (pairAct true) St.id w' = actList (pairAct true) St.id w) ∧
    (∃ w0, (∀ m ∈ w0, m ∈ pairH) ∧ ∀ w, (∀ m ∈ w, m ∈ pairH) →
        actList (pairAct true) St.id w = actList (pairAct true) St.id w0 → 8 ≤ w.length) :=
  god_number (by have := antiH_true; unfold antiHF at this; exact this)

#print axioms slice_group_quarter
#print axioms antislice_group_half
