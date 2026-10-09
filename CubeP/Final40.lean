import CubeP.Kph1Proof
import CubeP.Final
open Std

/-- **40-move bound**, formally: Kociemba's phase 1 (≤ 12) followed by Thistlethwaite's phases 3 (≤ 13) and
4 (≤ 15). Every position reachable with face turns is solved by at most 40 face turns. -/
theorem upper_bound_40 (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∃ W : List Nat, W.length ≤ 40 ∧ (∀ m ∈ W, m < 18) ∧ applyList (eval w) W = St.id := by
  obtain ⟨w1, l1, m1, e1, c1, k1⟩ := kociemba_phase1 w hw
  rw [← eval_append] at e1 c1 k1
  have hu1 := all_append hw m1
  have hk : key2 (eval (w ++ w1)) = key2 St.id := by
    show ((eval (w ++ w1)).co, maskOf (eval (w ++ w1)).ep) = (St.id.co, idE)
    rw [c1, k1]
  obtain ⟨w3, l3, m3, f1, f2, f3, f4, f5⟩ := phase3_htr (w ++ w1) hu1 e1 hk
  have m3' : ∀ m ∈ w3, m < 18 := fun m hm => g2_lt (m3 m hm)
  rw [← eval_append] at f1 f2 f3 f4 f5
  have hu3 := all_append hu1 m3'
  obtain ⟨w4, l4, m4, g⟩ := phase4_sq (w ++ w1 ++ w3) hu3 f1 f2 f3 f4 f5
  have m4' : ∀ m ∈ w4, m < 18 := fun m hm => half_lt (m4 m hm)
  refine ⟨w1 ++ w3 ++ w4, ?_, all_append (all_append m1 m3') m4', ?_⟩
  · simp only [List.length_append]; omega
  · rw [applyList_append, applyList_append, ← eval_append, ← eval_append]
    exact g

#print axioms upper_bound_40
