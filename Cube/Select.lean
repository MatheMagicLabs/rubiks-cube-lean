/-! Enumerating lists with entries from given candidate sets (pruned to duplicate-free lists), with a
correctness lemma. Independent of the cube. -/

def F2 : List Nat → List (List Nat) → Prop
  | [], [] => True
  | a :: l, A :: As => a ∈ A ∧ F2 l As
  | _, _ => False

def allSel : List (List Nat) → List Nat → (List Nat → Bool) → Bool
  | [], acc, P => P acc
  | A :: As, acc, P => A.all (fun a => if acc.contains a then true else allSel As (acc ++ [a]) P)

theorem allSel_spec : ∀ (As : List (List Nat)) (acc : List Nat) (P : List Nat → Bool),
    allSel As acc P = true → ∀ l, F2 l As → (acc ++ l).Nodup → P (acc ++ l) = true := by
  intro As
  induction As with
  | nil =>
    intro acc P h l hl _
    match l, hl with
    | [], _ => simpa [allSel] using h
  | cons A As ih =>
    intro acc P h l hl hn
    match l, hl with
    | a :: l', ⟨ha, hl'⟩ =>
      have h1 := (List.all_eq_true.1 h) a ha
      by_cases hc : acc.contains a = true
      · exfalso
        have hmem : a ∈ acc := List.contains_iff_mem.1 hc
        have : (acc ++ a :: l').Nodup := hn
        rw [List.nodup_append] at this
        exact this.2.2 a hmem a (by simp) rfl
      · have h2 : allSel As (acc ++ [a]) P = true := by
          simp only [hc] at h1
          simpa using h1
        have := ih (acc ++ [a]) P h2 l' hl' (by simpa using hn)
        simpa using this
