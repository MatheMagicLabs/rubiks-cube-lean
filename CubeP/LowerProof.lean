import CubeP.LowerThm
import CubeP.Kph1Proof
open Std

theorem lipFrom_spec (d : ByteArray) : ∀ n, lipFrom d n = true → ∀ i < n, lipCell d i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    unfold lipFrom at h
    split at h
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact ih h i h'
      · subst h'; assumption
    · exact absurd h (by simp)

theorem low_parts : lipFrom (distF ()) NN = true ∧ ((distF ()).get! i0).toNat = 0 ∧
    ((distF ()).get! (rank (eval k1Witness))).toNat = 12 := by
  have h := k1Low_true; unfold k1LowF at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lip_step (x : St) (hx : InC x) (m : Nat) (hm : m < 18) :
    ((distF ()).get! (rank x)).toNat ≤ ((distF ()).get! (rank (apply x m))).toNat + 1 := by
  have h := lipFrom_spec _ _ low_parts.1 (rank x) (rank_lt x hx)
  unfold lipCell at h
  have := (List.all_eq_true.1 h) m (List.mem_range.2 hm)
  rw [rank_apply x hx m hm]
  exact of_decide_eq_true this

theorem lip_reach (w : List Nat) (hw : ∀ m ∈ w, m < 18) : ∀ x, InC x →
    ((distF ()).get! (rank x)).toNat ≤ ((distF ()).get! (rank (applyList x w))).toNat + w.length := by
  induction w with
  | nil => intro x _; simp [applyList]
  | cons h w ih =>
    intro x hx
    have h1 := lip_step x hx h (hw h (by simp))
    have h2 := ih (fun m hm => hw m (by simp [hm])) (apply x h) (inC_apply hx h (hw h (by simp)))
    rw [applyList_cons']
    simp only [List.length_cons]; omega

/-- **Kociemba's phase 1 needs 12 moves in the worst case:** the position `k1Witness` cannot be brought into
<U,D,R2,L2,F2,B2>-form (edges and corners oriented, E-slice edges in the E slice) in fewer than 12 face turns. -/
theorem kociemba_phase1_lower (w : List Nat) (hw : ∀ m ∈ w, m < 18)
    (heo : (applyList (eval k1Witness) w).eo = eoZero) (hco : (applyList (eval k1Witness) w).co = St.id.co)
    (hmk : maskOf (applyList (eval k1Witness) w).ep = idE) : 12 ≤ w.length := by
  have hx : InC (eval k1Witness) := inC_applyList k1Witness (by
    intro m hm; have := k1Witness_valid; unfold k1WitnessValid at this
    exact of_decide_eq_true ((List.all_eq_true.1 this) m hm)) St.id inC_id
  have h := lip_reach w hw _ hx
  have hr : rank (applyList (eval k1Witness) w) = i0 := by
    unfold rank i0; rw [heo, hco, hmk]
  rw [hr, low_parts.2.1, low_parts.2.2] at h
  omega

#print axioms kociemba_phase1_lower
