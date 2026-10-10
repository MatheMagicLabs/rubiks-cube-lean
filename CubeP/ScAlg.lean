import CubeP.SfNorm
import CubeS.Sc
open Std

/-! Centre signatures for the supercube (quarter turns per face modulo 4) and the facts about them that the
normal form needs: invariance under cyclic shifts, rotations, merging and swapping commuting moves. -/

/-- quarter turns of face `f` in a word -/
def cnt (f : Nat) : List Nat → Nat
  | [] => 0
  | m :: w => (if m / 3 = f then m % 3 + 1 else 0) + cnt f w

theorem cnt_app (f : Nat) (a b : List Nat) : cnt f (a ++ b) = cnt f a + cnt f b := by
  induction a with
  | nil => simp [cnt]
  | cons m t ih => simp only [List.cons_append, cnt, ih]; omega

theorem cnt_ge6 {f : Nat} (hf : 6 ≤ f) : ∀ w : List Nat, (∀ m ∈ w, m < 18) → cnt f w = 0 := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons m t ih =>
    intro h
    have hm : m < 18 := h m (by simp)
    have := ih (fun k hk => h k (by simp [hk]))
    simp only [cnt, this]
    have : m / 3 ≠ f := by omega
    simp [this]

/-- the word turns every face centre by a multiple of 360° -/
def Z (w : List Nat) : Prop := ∀ f, cnt f w % 4 = 0

theorem Z_rot {a b : List Nat} (h : Z (a ++ b)) : Z (b ++ a) := by
  intro f; have := h f; rw [cnt_app] at this ⊢; omega

/-- swapping two adjacent moves keeps all counts -/
theorem cnt_swap (f : Nat) (u v : List Nat) (a b : Nat) : cnt f (u ++ a :: b :: v) = cnt f (u ++ b :: a :: v) := by
  rw [cnt_app, cnt_app]; simp only [cnt]; omega

theorem Z_swap {u v : List Nat} {a b : Nat} (h : Z (u ++ a :: b :: v)) : Z (u ++ b :: a :: v) := by
  intro f; rw [← cnt_swap]; exact h f

-- ---------- the signature computed by the search ----------
theorem sigOf_snoc (w : List Nat) (m : Nat) : sigOf (w ++ [m]) = sigStep (sigOf w) m := by
  unfold sigOf; rw [List.foldl_append]; rfl

theorem cnt_snoc (f : Nat) (w : List Nat) (m : Nat) :
    cnt f (w ++ [m]) = cnt f w + (if m / 3 = f then m % 3 + 1 else 0) := by
  rw [cnt_app]; simp [cnt]

/-- the search's signature is the vector of counts modulo 4 -/
theorem sigOf_spec : ∀ w : List Nat, (∀ m ∈ w, m < 18) →
    sigOf w = ⟨cnt 0 w % 4, cnt 1 w % 4, cnt 2 w % 4, cnt 3 w % 4, cnt 4 w % 4, cnt 5 w % 4⟩ := by
  intro w
  induction w using snoc_ind with
  | nil => intro _; rfl
  | append_singleton w m ih =>
    intro h
    have hm : m < 18 := h m (by simp)
    have ih' := ih (fun k hk => h k (by simp [hk]))
    rw [sigOf_snoc, ih']
    simp only [cnt_snoc]
    have h6 : m / 3 < 6 := by omega
    rcases (by omega : m / 3 = 0 ∨ m / 3 = 1 ∨ m / 3 = 2 ∨ m / 3 = 3 ∨ m / 3 = 4 ∨ m / 3 = 5) with
      e | e | e | e | e | e <;>
    · simp only [sigStep, e]
      simp only [Sig.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> omega

theorem Z_of_sig {w : List Nat} (hw : ∀ m ∈ w, m < 18) (h : sigOf w = sig0) : Z w := by
  rw [sigOf_spec w hw] at h
  simp only [sig0, Sig.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  intro f
  rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ 6 ≤ f) with
    rfl | rfl | rfl | rfl | rfl | rfl | hf
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · rw [cnt_ge6 hf w hw]

theorem sig_of_Z {w : List Nat} (hw : ∀ m ∈ w, m < 18) (h : Z w) : sigOf w = sig0 := by
  rw [sigOf_spec w hw]
  simp only [sig0, Sig.mk.injEq]
  exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩

-- ---------- moves: commuting, merging, rotations ----------
/-- finite facts: opposite faces commute; merging two moves of one face; rotations preserve the turn amount and
permute the faces -/
def scFactsB : Bool :=
  (List.range 18).all (fun a => (List.range 18).all (fun b =>
    !(a / 3 != b / 3 && (a / 3) % 3 == (b / 3) % 3) ||
      (moves[a]!).mul moves[b]! == (moves[b]!).mul moves[a]!)) &&
  (List.range 18).all (fun a => (List.range 18).all (fun b => a / 3 != b / 3 ||
    (if (a % 3 + b % 3 + 1) % 4 == 3 then (a % 3 + b % 3 + 2) % 4 == 0
     else mergeOf a b / 3 == a / 3 && (mergeOf a b % 3 + 1) % 4 == (a % 3 + b % 3 + 2) % 4))) &&
  ([muSArr, muYArr, muYiArr, muZArr].all (fun μa =>
    (List.range 18).all (fun m => μa[m]! % 3 == m % 3) &&
    (List.range 6).all (fun f => (List.range 6).any (fun g =>
      (List.range 18).all (fun m => (μa[m]! / 3 == f) == (m / 3 == g))))))
theorem scFacts_true : scFactsB = true := by native_decide

theorem commute_fact {a b : Nat} (ha : a < 18) (hb : b < 18) (hne : a / 3 ≠ b / 3) (hax : (a / 3) % 3 = (b / 3) % 3) :
    (moves[a]!).mul moves[b]! = (moves[b]!).mul moves[a]! := by
  have h := scFacts_true; unfold scFactsB at h
  simp only [Bool.and_eq_true] at h
  have := lt_of_range_all (lt_of_range_all h.1.1 ha) hb
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne,
    beq_iff_eq, ne_eq] at this
  rcases this with (h1 | h1) | h1
  · exact absurd h1 hne
  · exact absurd hax h1
  · exact h1

theorem merge_cnt {a b : Nat} (ha : a < 18) (hb : b < 18) (hf : a / 3 = b / 3) :
    ((a % 3 + b % 3 + 1) % 4 = 3 ∧ (a % 3 + b % 3 + 2) % 4 = 0) ∨
    ((a % 3 + b % 3 + 1) % 4 ≠ 3 ∧ mergeOf a b / 3 = a / 3 ∧ (mergeOf a b % 3 + 1) % 4 = (a % 3 + b % 3 + 2) % 4) := by
  have h := scFacts_true; unfold scFactsB at h
  simp only [Bool.and_eq_true] at h
  have := lt_of_range_all (lt_of_range_all h.1.2 ha) hb
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  rcases this with h1 | h1
  · exact absurd hf h1
  · split at h1
    · left; exact ⟨by simpa using (by assumption : (a % 3 + b % 3 + 1) % 4 == 3) , by simpa using h1⟩
    · right
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      refine ⟨?_, h1.1, h1.2⟩
      intro e; simp [e] at *

theorem rot_face {μa : Array Nat} (hμ : μa ∈ [muSArr, muYArr, muYiArr, muZArr]) :
    (∀ m < 18, μa[m]! % 3 = m % 3) ∧ ∀ f < 6, ∃ g, ∀ m < 18, (μa[m]! / 3 = f ↔ m / 3 = g) := by
  have h := scFacts_true; unfold scFactsB at h
  simp only [Bool.and_eq_true] at h
  have := List.all_eq_true.1 h.2 μa hμ
  simp only [Bool.and_eq_true] at this
  refine ⟨fun m hm => ?_, fun f hf => ?_⟩
  · have := lt_of_range_all this.1 hm; simpa using this
  · have h2 := lt_of_range_all this.2 hf
    obtain ⟨g, -, hg⟩ := List.any_eq_true.1 h2
    refine ⟨g, fun m hm => ?_⟩
    have := lt_of_range_all hg hm
    simp only [beq_iff_eq] at this
    exact ⟨fun e => by simpa [e] using this, fun e => by simp [e] at this; exact this⟩
