import CubeP.Low2ThmA
import CubeP.Low2ThmB
import CubeP.Kph2Proof
open Std

/-! **Kociemba's phase 2 needs 18 moves:** the mirror element cannot be solved in fewer than 18 moves of
⟨U, D, R2, L2, F2, B2⟩. Proof: phase-2 cells are invariant under the 16 symmetries, so the certified table is
1-Lipschitz along every phase-2 move, and the mirror element sits in a cell at distance 18. -/

theorem l2_parts : (∀ a < 16, ∀ b < 16, smul a b < 16) ∧
    (∀ k, cpG.contains k = true → ∀ a < 16, ∀ b < 16, conjC a (conjC b k) = conjC (smul a b) k) ∧
    (∀ k, epG.contains k = true → ∀ a < 16, ∀ b < 16, conjE a (conjE b k) = conjE (smul a b) k) ∧
    (∀ r < NCP, cpGI[cpGL[r]!]! = r) ∧ (∀ e < NE, epGI[epGL[e]!]! = e ∧ epCj[e * 16]! = e) ∧
    (∀ c < NC, clsT[repsT[c]!]! = c ∧ ∀ u < 16, clsT[cpGI[conjC u cpGL[repsT[c]!]!]!]! = c ∧
      (conjC u cpGL[repsT[c]!]! ≠ cpGL[repsT[c]!]! ∨ u = 0 ∨ u ∈ stabT[c]!)) := by
  have h := low2Facts_true; unfold low2FactsF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun a ha b hb => ?_, fun k hk a ha b hb => ?_, fun k hk a ha b hb => ?_, fun r hr => ?_,
    fun e he => ?_, fun c hc => ?_⟩
  · exact of_decide_eq_true (lt_of_range_all (lt_of_range_all h1 ha) hb)
  · have := lt_of_range_all (lt_of_range_all ((List.all_eq_true.1 h2) (k, ()) (mem_toList_of_contains hk)) ha) hb
    simpa using this
  · have := lt_of_range_all (lt_of_range_all ((List.all_eq_true.1 h3) (k, ()) (mem_toList_of_contains hk)) ha) hb
    simpa using this
  · simpa using lt_of_range_all h4 hr
  · have := lt_of_range_all h5 he
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this
  · have := lt_of_range_all h6 hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
      ne_eq, List.contains_iff_mem] at this
    refine ⟨this.1, fun u hu => ?_⟩
    obtain ⟨a1, a2⟩ := this.2 u hu
    refine ⟨a1, ?_⟩
    rcases a2 with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem canon_inv {c e u : Nat} (hc : c < NC) (he : e < NE) (hu : u ∈ stabT[c]!) :
    canon c epCj[e * 16 + u]! = canon c e := by
  have h := lt_of_range_all canonInv_true hc
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · have hne : stabT[c]! ≠ [] := List.ne_nil_of_mem hu
    exact absurd (List.isEmpty_iff.1 h) hne
  · have := (List.all_eq_true.1 (lt_of_range_all h he)) u hu
    simpa using this

theorem conjC3 {k : Array Nat} (hk : cpG.contains k = true) {a b c : Nat} (ha : a < 16) (hb : b < 16) (hc : c < 16) :
    conjC a (conjC b (conjC c k)) = conjC (smul a (smul b c)) k := by
  rw [l2_parts.2.1 k hk b hb c hc, l2_parts.2.1 k hk a ha _ (l2_parts.1 b hb c hc)]
theorem conjE3 {k : Array Nat} (hk : epG.contains k = true) {a b c : Nat} (ha : a < 16) (hb : b < 16) (hc : c < 16) :
    conjE a (conjE b (conjE c k)) = conjE (smul a (smul b c)) k := by
  rw [l2_parts.2.2.1 k hk b hb c hc, l2_parts.2.2.1 k hk a ha _ (l2_parts.1 b hb c hc)]

/-- a cell is determined by any single conjugate of the element that is in canonical form -/
theorem cell_unique {p : P} (hp : Dom p) {c e u : Nat} (hc : c < NC) (he : e < NE) (hcan : canon c e = e)
    (hu : u < 16) (h1 : cpGL[repsT[c]!]! = conjC u p.1) (h2 : epGL[e]! = conjE u p.2) : cellOf p = c * NE + e := by
  obtain ⟨c', e', σ, t, hc', he', hσ, ht, hcell, hcan', -, hcp, hep⟩ := cell_facts hp
  have iu := inv_parts.1 u hu
  have hrc : cpG.contains cpGL[repsT[c]!]! = true := cpGL_in (reps_lt hc)
  have hre : epG.contains epGL[e]! = true := epGL_in he
  have hp1 : p.1 = conjC invS[u]! cpGL[repsT[c]!]! := by rw [h1, inv_parts.2.1 _ hp.1 u hu]
  have hp2 : p.2 = conjE invS[u]! epGL[e]! := by rw [h2, inv_parts.2.2 _ hp.2 u hu]
  let v := smul t (smul σ invS[u]!)
  have hv : v < 16 := l2_parts.1 t ht _ (l2_parts.1 σ hσ _ iu)
  have hcp' : cpGL[repsT[c']!]! = conjC v cpGL[repsT[c]!]! := by rw [hcp, hp1, conjC3 hrc ht hσ iu]
  have hep' : epGL[e']! = conjE v epGL[e]! := by rw [hep, hp2, conjE3 hre ht hσ iu]
  -- classes agree
  have hcl := (l2_parts.2.2.2.2.2 c hc).2 v hv
  have hidx : cpGI[conjC v cpGL[repsT[c]!]!]! = repsT[c']! := by
    rw [← hcp']; exact l2_parts.2.2.2.1 _ (reps_lt hc')
  have hcc : c' = c := by
    have e1 := (l2_parts.2.2.2.2.2 c' hc').1
    rw [← e1, ← hidx]; exact hcl.1
  subst hcc
  -- edges
  have hee : e' = epCj[e * 16 + v]! := by
    rw [(mvE he (j := 0) (by decide) hv).2, ← hep', (l2_parts.2.2.2.2.1 e' he').1]
  have hfix : conjC v cpGL[repsT[c']!]! = cpGL[repsT[c']!]! := hcp'.symm
  rcases hcl.2 with hne | hv0 | hst
  · exact absurd hfix hne
  · rw [hcell, hee, hv0, show e * 16 + 0 = e * 16 by omega, (l2_parts.2.2.2.2.1 e he).2]
  · rw [hcell, ← hcan', hee, canon_inv hc' he hst, hcan]

/-- cells are invariant under the 16 symmetries -/
theorem cellOf_conj {p : P} (hp : Dom p) {s : Nat} (hs : s < 16) : cellOf (conjP s p) = cellOf p := by
  obtain ⟨c, e, σ, t, hc, he, hσ, ht, hcell, hcan, -, hcp, hep⟩ := cell_facts hp
  have is := inv_parts.1 s hs
  have hq := dom_conj hp hs
  have hp1 : p.1 = conjC invS[s]! (conjP s p).1 := (inv_parts.2.1 _ hp.1 s hs).symm
  have hp2 : p.2 = conjE invS[s]! (conjP s p).2 := (inv_parts.2.2 _ hp.2 s hs).symm
  rw [hcell]
  apply cell_unique hq hc he hcan (l2_parts.1 t ht _ (l2_parts.1 σ hσ _ is))
  · rw [hcp, hp1, conjC3 hq.1 ht hσ is]
  · rw [hep, hp2, conjE3 hq.2 ht hσ is]

theorem g2_idx : ∀ m ∈ g2Moves, ∃ j < 10, g2A[j]! = m := by decide

theorem lip2From_succ (d : ByteArray) (n : Nat) :
    lip2From d (n + 1) = if lipCell2 d n then lip2From d n else false := rfl
theorem lip2From_spec (d : ByteArray) : ∀ n, lip2From d n = true → ∀ i < n, lipCell2 d i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    rw [lip2From_succ] at h
    by_cases hc : lipCell2 d n = true
    · rw [if_pos hc] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact ih h i h'
      · rw [h']; exact hc
    · rw [if_neg hc] at h; exact absurd h (by simp)

theorem low2_parts : lip2From (dist2F ()) N2 = true ∧ ((dist2F ()).get! idCell).toNat = 0 ∧
    cpG.contains mirrorP.1 = true ∧ epG.contains mirrorP.2 = true ∧ ((dist2F ()).get! (cellOf mirrorP)).toNat = 18 := by
  have h := low2_true; unfold low2F at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
  exact ⟨a, b, c, d, e⟩

/-- the table is 1-Lipschitz along every phase-2 move, for every element -/
theorem lip2_step {p : P} (hp : Dom p) {m : Nat} (hm : m ∈ g2Moves) :
    ((dist2F ()).get! (cellOf p)).toNat ≤ ((dist2F ()).get! (cellOf (pAct p m))).toNat + 1 := by
  obtain ⟨c, e, σ, t, hc, he, hσ, ht, hcell, -, hst, -, -⟩ := cell_facts hp
  obtain ⟨hlt, hcan⟩ := cellOf_can hp
  have hm1 := (compC hp.1 hσ hm).2
  have hm2 := (compC (dom_conj hp hσ).1 ht hm1).2
  obtain ⟨j, hj, hjm⟩ := g2_idx _ hm2
  have hn : nextC (cellOf p) j = cellOf (pAct p m) := by
    rw [hcell, nextC_eq hc he hj, ← hcell, hst, hjm, ← conj_act (dom_conj hp hσ) ht hm1, ← conj_act hp hσ hm,
      cellOf_conj (dom_conj (dom_act hp hm) hσ) ht, cellOf_conj (dom_act hp hm) hσ]
  have h := lip2From_spec _ _ low2_parts.1 _ hlt
  unfold lipCell2 at h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with h | h
  · exact absurd hcan h
  · have := lt_of_range_all h hj
    rw [hn] at this
    exact of_decide_eq_true this

theorem lip2_reach (W : List Nat) (hw : ∀ m ∈ W, m ∈ g2Moves) : ∀ p, Dom p →
    ((dist2F ()).get! (cellOf p)).toNat ≤ ((dist2F ()).get! (cellOf (pActList p W))).toNat + W.length := by
  induction W with
  | nil => intro p _; exact Nat.le_add_right _ _
  | cons m W ih =>
    intro p hp
    have hm : m ∈ g2Moves := hw m (by simp)
    have h1 := lip2_step hp hm
    have h2 := ih (fun k hk => hw k (by simp [hk])) _ (dom_act hp hm)
    rw [pActList_cons, List.length_cons]
    generalize ((dist2F ()).get! (cellOf p)).toNat = a at *
    generalize ((dist2F ()).get! (cellOf (pAct p m))).toNat = b at *
    generalize ((dist2F ()).get! (cellOf (pActList (pAct p m) W))).toNat = c at *
    omega

/-- **Kociemba's phase 2 needs 18 moves (on permutation pairs).** -/
theorem phase2_lower_P (W : List Nat) (hw : ∀ m ∈ W, m ∈ g2Moves) (h : pActList mirrorP W = idP) :
    18 ≤ W.length := by
  have hd : Dom mirrorP := ⟨low2_parts.2.2.1, low2_parts.2.2.2.1⟩
  have := lip2_reach W hw mirrorP hd
  rw [h, low2_parts.2.2.2.2] at this
  have h0 : cellOf idP = idCell := rfl
  rw [h0, low2_parts.2.1] at this
  generalize W.length = n at *
  omega

/-- the mirror position as a cube state: corners and edges oriented, U/D layers reflected left–right -/
def mirrorSt : St := ⟨mirrorP.1, St.id.co, mirrorP.2, St.id.eo⟩

/-- **Kociemba's phase 2 needs 18 moves:** the mirror position (a domino-reduced position) is not solved by any
word of fewer than 18 moves of ⟨U, D, R2, L2, F2, B2⟩. With `kociemba_phase2` this makes 18 the exact maximum. -/
theorem kociemba_phase2_lower (W : List Nat) (hw : ∀ m ∈ W, m ∈ g2Moves) (h : applyList mirrorSt W = St.id) :
    18 ≤ W.length := by
  apply phase2_lower_P W hw
  have := applyList_pact W mirrorSt
  rw [h] at this
  exact this.symm

#print axioms kociemba_phase2_lower

/-- an 18-move word of ⟨U,D,R2,L2,F2,B2⟩ producing the mirror position (found by descent in the certified table) -/
def mirrorWord : List Nat := [7, 13, 0, 16, 7, 4, 16, 7, 4, 0, 7, 4, 9, 0, 7, 4, 11, 2]
theorem mirrorWord_ok : (mirrorWord.length == 18 && mirrorWord.all (fun m => g2Moves.contains m) &&
    eval mirrorWord == mirrorSt) = true := by native_decide

/-- **The phase-2 bound 18 is attained:** the mirror position is reached by 18 moves of ⟨U,D,R2,L2,F2,B2⟩ and
cannot be solved by fewer. -/
theorem kociemba_phase2_attained : (∃ w : List Nat, (∀ m ∈ w, m ∈ g2Moves) ∧ eval w = mirrorSt) ∧
    ∀ W, (∀ m ∈ W, m ∈ g2Moves) → applyList mirrorSt W = St.id → 18 ≤ W.length := by
  have h := mirrorWord_ok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨⟨mirrorWord, h.1.2, h.2⟩, kociemba_phase2_lower⟩

#print axioms kociemba_phase2_attained
