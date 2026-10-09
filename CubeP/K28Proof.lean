import CubeP.Kph2Proof
import CubeP.K28ThmA
import CubeP.K28ThmB1
import CubeP.K28ThmB2
import CubeP.K28ThmC
open Std

/-! The 28-move bound. Phase-1 distance ≤ 10: phases 1 + 2 directly. Distance 11: two 11-move phase-1 words per
coset whose difference avoids all differences of two phase-2 elements at distance 18. Distance 12: several
12-move words whose differences move every phase-2 element at distance ≥ 17 to one at distance ≤ 16. -/

-- ---------- arrays over `List.range` ----------
theorem gmr {n : Nat} {f : Nat → Nat} {i : Nat} (hi : i < n) : ((List.range n).toArray.map f)[i]! = f i := by
  rw [getElem!_pos _ i (by simp; omega)]; simp

theorem map_range_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    (List.range n).toArray.map f = (List.range n).toArray.map g := by
  apply Array.ext
  · simp
  · intro i h1 _
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
    exact h i (by simpa using h1)

theorem map_range_self {n : Nat} {a : Array Nat} (ha : a.size = n) : (List.range n).toArray.map (fun i => a[i]!) = a := by
  apply Array.ext
  · simp [ha]
  · intro i h1 h2
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range]
    rw [getElem!_pos a i h2]

def mvBnd : Bool := (List.range 18).all (fun m =>
  (List.range 8).all (fun i => decide ((moves[m]!).cp[i]! < 8)) && (List.range 12).all (fun i => decide ((moves[m]!).ep[i]! < 12)))
theorem mvBnd_true : mvBnd = true := by native_decide

theorem mvb {m : Nat} (hm : m < 18) : (∀ i < 8, (moves[m]!).cp[i]! < 8) ∧ (∀ i < 12, (moves[m]!).ep[i]! < 12) := by
  have h := lt_of_range_all mvBnd_true hm
  simp only [Bool.and_eq_true] at h
  exact ⟨fun i hi => of_decide_eq_true (lt_of_range_all h.1 hi), fun i hi => of_decide_eq_true (lt_of_range_all h.2 hi)⟩

theorem idc : ∀ i < 8, St.id.cp[i]! = i := by decide
theorem ide : ∀ i < 12, St.id.ep[i]! = i := by decide

-- ---------- composition ----------
theorem pAct_pmul (p q : P) {m : Nat} (hm : m < 18) : pAct (pmul p q) m = pmul p (pAct q m) := by
  obtain ⟨hc, he⟩ := mvb hm
  have e1 : cpAct (pmul p q).1 m = (pmul p (pAct q m)).1 := by
    change (List.range 8).toArray.map (fun i => ((List.range 8).toArray.map (fun j => p.1[q.1[j]!]!))[(moves[m]!).cp[i]!]!) =
      (List.range 8).toArray.map (fun i => p.1[((List.range 8).toArray.map (fun j => q.1[(moves[m]!).cp[j]!]!))[i]!]!)
    apply map_range_congr; intro i hi; rw [gmr (hc i hi), gmr hi]
  have e2 : epAct (pmul p q).2 m = (pmul p (pAct q m)).2 := by
    change (List.range 12).toArray.map (fun i => ((List.range 12).toArray.map (fun j => p.2[q.2[j]!]!))[(moves[m]!).ep[i]!]!) =
      (List.range 12).toArray.map (fun i => p.2[((List.range 12).toArray.map (fun j => q.2[(moves[m]!).ep[j]!]!))[i]!]!)
    apply map_range_congr; intro i hi; rw [gmr (he i hi), gmr hi]
  exact Prod.ext e1 e2

theorem pActList_pmul (p : P) : ∀ w : List Nat, (∀ m ∈ w, m < 18) → ∀ q, pActList (pmul p q) w = pmul p (pActList q w) := by
  intro w
  induction w with
  | nil => intro _ q; rfl
  | cons m w ih =>
    intro hw q
    rw [pActList_cons, pActList_cons, pAct_pmul p q (hw m (by simp))]
    exact ih (fun m' hm' => hw m' (by simp [hm'])) _

theorem pmul_idR (p : P) (h1 : p.1.size = 8) (h2 : p.2.size = 12) : pmul p idP = p := by
  unfold pmul idP
  have e1 : (List.range 8).toArray.map (fun i => p.1[St.id.cp[i]!]!) = (List.range 8).toArray.map (fun i => p.1[i]!) :=
    map_range_congr (fun i hi => by rw [idc i hi])
  have e2 : (List.range 12).toArray.map (fun i => p.2[St.id.ep[i]!]!) = (List.range 12).toArray.map (fun i => p.2[i]!) :=
    map_range_congr (fun i hi => by rw [ide i hi])
  simp only [e1, e2, map_range_self h1, map_range_self h2]

theorem bnd_parts {k : P} (hk : bndOk k = true) :
    k.1.size = 8 ∧ k.2.size = 12 ∧ (∀ i < 8, k.1[i]! < 8) ∧ (∀ i < 12, k.2[i]! < 12) := by
  unfold bndOk at hk
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hk
  refine ⟨h1, h2, fun i hi => ?_, fun i hi => ?_⟩
  · rw [getElem!_pos k.1 i (by omega)]; exact h3 i (by omega)
  · rw [getElem!_pos k.2 i (by omega)]; exact h4 i (by omega)

theorem pmul_assoc (a b c : P) (hc : bndOk c = true) : pmul (pmul a b) c = pmul a (pmul b c) := by
  obtain ⟨-, -, h3, h4⟩ := bnd_parts hc
  have e1 : (pmul (pmul a b) c).1 = (pmul a (pmul b c)).1 := by
    change (List.range 8).toArray.map (fun i => ((List.range 8).toArray.map (fun j => a.1[b.1[j]!]!))[c.1[i]!]!) =
      (List.range 8).toArray.map (fun i => a.1[((List.range 8).toArray.map (fun j => b.1[c.1[j]!]!))[i]!]!)
    apply map_range_congr; intro i hi; rw [gmr (h3 i hi), gmr hi]
  have e2 : (pmul (pmul a b) c).2 = (pmul a (pmul b c)).2 := by
    change (List.range 12).toArray.map (fun i => ((List.range 12).toArray.map (fun j => a.2[b.2[j]!]!))[c.2[i]!]!) =
      (List.range 12).toArray.map (fun i => a.2[((List.range 12).toArray.map (fun j => b.2[c.2[j]!]!))[i]!]!)
    apply map_range_congr; intro i hi; rw [gmr (h4 i hi), gmr hi]
  exact Prod.ext e1 e2

theorem pmul_idL (k : P) (hk : bndOk k = true) : pmul idP k = k := by
  obtain ⟨h1, h2, h3, h4⟩ := bnd_parts hk
  unfold pmul idP
  have e1 : (List.range 8).toArray.map (fun i => St.id.cp[k.1[i]!]!) = (List.range 8).toArray.map (fun i => k.1[i]!) :=
    map_range_congr (fun i hi => by rw [idc _ (h3 i hi)])
  have e2 : (List.range 12).toArray.map (fun i => St.id.ep[k.2[i]!]!) = (List.range 12).toArray.map (fun i => k.2[i]!) :=
    map_range_congr (fun i hi => by rw [ide _ (h4 i hi)])
  simp only [e1, e2, map_range_self h1, map_range_self h2]

theorem pmul_cancel (y k : P) (hy : pmul (pinv y) y = idP) (hk : bndOk k = true) : pmul (pinv y) (pmul y k) = k := by
  rw [← pmul_assoc _ _ _ hk, hy, pmul_idL k hk]

-- ---------- phase 1: words and their endpoints ----------
theorem nextList_cons (i m : Nat) (w : List Nat) : nextList i (m :: w) = nextList (next i m) w := rfl

theorem rank_list (w : List Nat) (hw : ∀ m ∈ w, m < 18) : ∀ x, InC x → rank (applyList x w) = nextList (rank x) w := by
  induction w with
  | nil => intro x _; rfl
  | cons m w ih =>
    intro x hx
    rw [applyList_cons', nextList_cons, ← rank_apply x hx m (hw m (by simp))]
    exact ih (fun m' hm' => hw m' (by simp [hm'])) _ (inC_apply hx m (hw m (by simp)))

theorem wordOk_parts {i L : Nat} {w : List Nat} (h : wordOk i L w = true) :
    w.length = L ∧ (∀ m ∈ w, m < 18) ∧ nextList i w = i0 := by
  unfold wordOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- what a certified phase-1 word does to a position -/
theorem after_word (w0 w : List Nat) (h0 : ∀ m ∈ w0, m < 18) (L : Nat) (hok : wordOk (rank (eval w0)) L w = true) :
    w.length = L ∧ (∀ m ∈ w, m < 18) ∧ Good (applyList (eval w0) w) ∧
    (applyList (eval w0) w).eo = eoZero ∧ (applyList (eval w0) w).co = St.id.co ∧
    maskOf (applyList (eval w0) w).ep = idE ∧ cpSet.contains (applyList (eval w0) w).cp = true ∧
    ((applyList (eval w0) w).cp, (applyList (eval w0) w).ep) = pmul ((eval w0).cp, (eval w0).ep) (pActList idP w) := by
  obtain ⟨hl, hw, hn⟩ := wordOk_parts hok
  have hu := all_append h0 hw
  have hx : InC (eval w0) := inC_applyList w0 h0 St.id inC_id
  have hr : rank (applyList (eval w0) w) = i0 := by rw [rank_list w hw _ hx, hn]
  obtain ⟨e1, e2, e3⟩ := rank_eq_i0 _ (inC_applyList w hw _ hx) hr
  have hg0 := parity_law w0 h0
  refine ⟨hl, hw, by rw [← eval_append]; exact parity_law _ hu, e1, e2, e3,
    by rw [← eval_append]; exact cp_reach _ hu St.id cpId_true, ?_⟩
  rw [applyList_pact, ← pActList_pmul _ w hw, pmul_idR _ hg0.1 hg0.2.1]

-- ---------- phase 2 with the table value as bound ----------
theorem dr_dom (x : St) (hg : Good x) (hmk : maskOf x.ep = idE) (hcp : cpSet.contains x.cp = true) :
    Dom (x.cp, x.ep) ∧ parC (cellOf (x.cp, x.ep)) = 0 := by
  have hs := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2; unfold startOk at hs
  simp only [Bool.and_eq_true] at hs
  have hdc : cpG.contains x.cp = true := by
    have := (List.all_eq_true.1 hs.1.1) (x.cp, ()) (mem_toList_of_contains hcp); simpa using this
  have hF : F2 x.ep.toList sliceSets2 := F2_of _ _ (by simp [sliceSets2, hg.2.1]) (ep_slice x hg hmk)
  have hnd : x.ep.toList.Nodup := hg.2.2.2.1.nodup_iff.2 List.nodup_range
  have hde : epG.contains x.ep = true := by
    have := allSel_spec sliceSets2 [] _ hs.1.2 x.ep.toList hF (by simpa using hnd)
    simpa using this
  have hp : Dom (x.cp, x.ep) := ⟨hdc, hde⟩
  refine ⟨hp, ?_⟩
  obtain ⟨c, e, σ, t, hc, he, hσ, ht, hcell, -, -, hcr, her⟩ := cell_facts hp
  rw [hcell]; unfold parC
  have h1 : (c * NE + e) / NE = c := by unfold NE at *; omega
  have h2 : (c * NE + e) % NE = e := by unfold NE at *; omega
  have hdc' : cpG.contains (conjC σ x.cp) = true := (closedC_parts hdc).2 _ hσ
  have hde' : epG.contains (conjE σ x.ep) = true := (closedE_parts hde).2 _ hσ
  rw [h1, h2, par_parts.2.2.1 c hc, par_parts.2.2.2 e he, hcr, her,
    par_parts.1 _ hdc' t ht, par_parts.2.1 _ hde' t ht,
    par_parts.1 _ hdc σ hσ, par_parts.2.1 _ hde σ hσ]
  have := hg.2.2.2.2; omega

theorem phase2_cell (x : St) (hg : Good x) (heo : x.eo = eoZero) (hco : x.co = St.id.co)
    (hmk : maskOf x.ep = idE) (hcp : cpSet.contains x.cp = true) :
    ((dist2F ()).get! (cellOf (x.cp, x.ep))).toNat ≤ 18 ∧
    ∃ W, W.length ≤ ((dist2F ()).get! (cellOf (x.cp, x.ep))).toNat ∧ (∀ m ∈ W, m < 18) ∧ applyList x W = St.id := by
  obtain ⟨hp, hpar⟩ := dr_dom x hg hmk hcp
  obtain ⟨hlt, hcan⟩ := cellOf_can hp
  refine ⟨(cell2 _ hlt hpar hcan).1, ?_⟩
  obtain ⟨W, hl, hw, hpw⟩ := g2_descent _ _ hp hpar rfl
  refine ⟨W, hl, fun m hm => g2_lt (hw m hm), ?_⟩
  have hpe := applyList_pact W x
  rw [hpw] at hpe
  obtain ⟨e1, e2, -⟩ := g2_keep W hw x heo hco hmk
  have hcp' : (applyList x W).cp = St.id.cp := congrArg Prod.fst hpe
  have hep' : (applyList x W).ep = St.id.ep := congrArg Prod.snd hpe
  revert e1 e2 hcp' hep'
  generalize applyList x W = y
  intro e1 e2 hcp' hep'
  cases y
  simp only at e1 e2 hcp' hep'
  rw [e1, e2, hcp', hep']; rfl

/-- every element of a cell is a double conjugate of the cell's representative -/
theorem bad_repr (p : P) (hp : Dom p) : cellOf p < N2 ∧ ∃ a b, a < 16 ∧ b < 16 ∧ p = conjP a (conjP b (stateOf (cellOf p))) := by
  obtain ⟨c, e, σ, t, hc, he, hσ, ht, hcell, -, hst, -, -⟩ := cell_facts hp
  obtain ⟨hlt, -⟩ := cellOf_can hp
  refine ⟨hlt, invS[σ]!, invS[t]!, inv_parts.1 σ hσ, inv_parts.1 t ht, ?_⟩
  rw [hst, conj_inv (dom_conj hp hσ) ht, conj_inv hp hσ]

-- ---------- the certificates ----------
theorem allBelow_succ (f : Nat → Bool) (n : Nat) : allBelow f (n + 1) = if f n then allBelow f n else false := rfl
theorem allBelow_spec (f : Nat → Bool) : ∀ n, allBelow f n = true → ∀ i < n, f i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    rw [allBelow_succ] at h
    by_cases hc : f n = true
    · rw [if_pos hc] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact ih h i h'
      · rw [h']; exact hc
    · rw [if_neg hc] at h; exact absurd h (by simp)

theorem h3_at (i : Nat) (hi : i < NN) :
    (((distF ()).get! i).toNat = 11 → cert11 (distF ()) (kbadF ()) i = true) ∧
    (((distF ()).get! i).toNat = 12 → words476.contains i = true) := by
  have key : ((((distF ()).get! i).toNat != 11 || cert11 (distF ()) (kbadF ()) i) &&
      (((distF ()).get! i).toNat != 12 || words476.contains i)) = true := by
    by_cases hh : i < HALF
    · have h := h3a_true; unfold h3F at h
      have := allBelow_spec _ _ h i hh
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h0 | h0
      · omega
      · exact h0
    · have h := h3b_true; unfold h3F at h
      have := allBelow_spec _ _ h i hi
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h0 | h0
      · exact absurd h0 hh
      · exact h0
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at key
  refine ⟨fun h11 => ?_, fun h12 => ?_⟩
  · rcases key.1 with h' | h'
    · exact absurd h11 h'
    · exact h'
  · rcases key.2 with h' | h'
    · exact absurd h12 h'
    · exact h'

theorem h1_parts : allBelow (badCellOk (dist2F ()) (bad17F (dist2F ()))) N2 = true ∧
    words476.toList.all (fun p => cert12 (dist2F ()) (bad17F (dist2F ())) p.1 p.2) = true := by
  have h := h1_true; unfold h1F at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem h4_parts : (∀ y, bad18S.contains y = true → bndOk y = true ∧ pmul (pinv y) y = idP) ∧
    (∀ y y', bad18S.contains y = true → bad18S.contains y' = true → (kbadF ()).contains (pmul (pinv y) y') = true) := by
  have h := h4_true; unfold h4F at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun y hy => ?_, fun y y' hy hy' => ?_⟩
  · have := (List.all_eq_true.1 h.1) (y, ()) (mem_toList_of_contains hy)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this
  · have := (List.all_eq_true.1 ((List.all_eq_true.1 h.2) (y, ()) (mem_toList_of_contains hy))) (y', ()) (mem_toList_of_contains hy')
    simpa using this

/-- an element at phase-2 table distance ≥ 17 (resp. 18) lies in the certified bad set -/
theorem bad_mem (p : P) (hp : Dom p) :
    (((dist2F ()).get! (cellOf p)).toNat = 17 ∨ ((dist2F ()).get! (cellOf p)).toNat = 18 →
      (bad17F (dist2F ())).contains p = true) ∧
    (((dist2F ()).get! (cellOf p)).toNat = 18 → bad18S.contains p = true) := by
  obtain ⟨hlt, a, b, ha, hb, hpe⟩ := bad_repr p hp
  have h := allBelow_spec _ _ h1_parts.1 _ hlt
  unfold badCellOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq,
    List.all_eq_true, List.mem_range] at h
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · rcases h.1 with h' | h'
    · simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h'
      rcases hv with hv | hv
      · exact absurd hv h'.1
      · exact absurd hv h'.2
    · rw [hpe]; exact h' a ha b hb
  · rcases h.2 with h' | h'
    · exact absurd hv h'
    · rw [hpe]; exact h' a ha b hb

-- ---------- the theorem ----------
/-- **28-move bound**, formally: every position reachable with face turns is solved by at most 28 face turns. -/
theorem upper_bound_28 (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∃ W : List Nat, W.length ≤ 28 ∧ (∀ m ∈ W, m < 18) ∧ applyList (eval w) W = St.id := by
  have hx : InC (eval w) := inC_applyList w hw St.id inC_id
  have hi : rank (eval w) < NN := rank_lt _ hx
  have hle := (cell _ hi).1
  -- finishing step: a phase-1 word followed by a phase-2 solution
  have fin : ∀ (w1 W : List Nat), (∀ m ∈ w1, m < 18) → (∀ m ∈ W, m < 18) →
      applyList (applyList (eval w) w1) W = St.id → w1.length + W.length ≤ 28 →
      ∃ W' : List Nat, W'.length ≤ 28 ∧ (∀ m ∈ W', m < 18) ∧ applyList (eval w) W' = St.id :=
    fun w1 W h1 h2 h3 h4 => ⟨w1 ++ W, by simpa using h4, all_append h1 h2, by rw [applyList_append]; exact h3⟩
  by_cases h10 : ((distF ()).get! (rank (eval w))).toNat ≤ 10
  · obtain ⟨w1, l1, m1, r1⟩ := descent _ (eval w) hx rfl
    obtain ⟨e1, c1, k1⟩ := rank_eq_i0 _ (inC_applyList w1 m1 _ hx) r1
    rw [← eval_append] at e1 c1 k1
    have hu := all_append hw m1
    obtain ⟨W, lW, mW, gW⟩ := kociemba_phase2 _ (parity_law _ hu) e1 c1 k1 (cp_reach _ hu St.id cpId_true)
    rw [eval_append] at gW
    exact fin w1 W m1 (fun m hm => g2_lt (mW m hm)) gW (by omega)
  · have hv : ((distF ()).get! (rank (eval w))).toNat = 11 ∨ ((distF ()).get! (rank (eval w))).toNat = 12 := by omega
    obtain ⟨h11, h12⟩ := h3_at _ hi
    have hg0 := parity_law w hw
    rcases hv with hv | hv
    · -- distance 11: a certified pair of words
      have hc := h11 hv
      unfold cert11 at hc
      revert hc
      generalize pair11 (distF ()) (kbadF ()) (rank (eval w)) = q
      intro hc
      cases q with
      | none => exact absurd hc (by simp)
      | some pr =>
        obtain ⟨w1, w2⟩ := pr
        simp only at hc
        unfold pairOk at hc
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨⟨hw1, hw2⟩, ⟨hK, hbk⟩, hnk⟩ := hc
        obtain ⟨l1, m1, g1, e1, c1, k1, p1, P1⟩ := after_word w w1 hw 11 hw1
        obtain ⟨l2, m2, g2, e2, c2, k2, p2, P2⟩ := after_word w w2 hw 11 hw2
        obtain ⟨b1, W1, lW1, mW1, gW1⟩ := phase2_cell _ g1 e1 c1 k1 p1
        obtain ⟨b2, W2, lW2, mW2, gW2⟩ := phase2_cell _ g2 e2 c2 k2 p2
        by_cases f1 : ((dist2F ()).get! (cellOf ((applyList (eval w) w1).cp, (applyList (eval w) w1).ep))).toNat ≤ 17
        · exact fin w1 W1 m1 mW1 gW1 (by omega)
        by_cases f2 : ((dist2F ()).get! (cellOf ((applyList (eval w) w2).cp, (applyList (eval w) w2).ep))).toNat ≤ 17
        · exact fin w2 W2 m2 mW2 gW2 (by omega)
        exfalso
        -- both endpoints at distance 18: their difference would be a bad difference
        have d1 := (dr_dom _ g1 k1 p1).1
        have d2 := (dr_dom _ g2 k2 p2).1
        have bb1 := (bad_mem _ d1).2 (by omega)
        have bb2 := (bad_mem _ d2).2 (by omega)
        have hp2 : ((applyList (eval w) w2).cp, (applyList (eval w) w2).ep) =
            pmul ((applyList (eval w) w1).cp, (applyList (eval w) w1).ep)
              (pmul (pinv (pActList idP w1)) (pActList idP w2)) := by
          rw [P2, P1, pmul_assoc _ _ _ hbk, hK]
        have hkin := h4_parts.2 _ _ bb1 bb2
        rw [hp2, pmul_cancel _ _ (h4_parts.1 _ bb1).2 hbk] at hkin
        rw [hkin] at hnk
        exact absurd hnk (by simp)
    · -- distance 12: the listed words
      have hc := h12 hv
      rw [HashMap.contains_eq_isSome_getElem?] at hc
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.1 hc
      have hmem : (rank (eval w), ws) ∈ words476.toList := (HashMap.mem_toList_iff_getElem?_eq_some).2 hws
      have h12c := (List.all_eq_true.1 h1_parts.2) _ hmem
      simp only at h12c
      unfold cert12 at h12c
      cases ws with
      | nil => exact absurd h12c (by simp)
      | cons w0 rest =>
        simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq, beq_iff_eq] at h12c
        obtain ⟨⟨hw0, hrest⟩, hcov⟩ := h12c
        obtain ⟨l0, m0, g0, e0, c0, k0, p0, P0⟩ := after_word w w0 hw 12 hw0
        obtain ⟨b0, W0, lW0, mW0, gW0⟩ := phase2_cell _ g0 e0 c0 k0 p0
        by_cases f0 : ((dist2F ()).get! (cellOf ((applyList (eval w) w0).cp, (applyList (eval w) w0).ep))).toNat ≤ 16
        · exact fin w0 W0 m0 mW0 gW0 (by omega)
        have d0 := (dr_dom _ g0 k0 p0).1
        have bb := (bad_mem _ d0).1 (by omega)
        obtain ⟨k, hk, hk16⟩ := hcov _ (mem_toList_of_contains bb)
        obtain ⟨wj, hwj, rfl⟩ := List.mem_map.1 hk
        obtain ⟨hwjok, hKj, hbkj⟩ := hrest wj hwj
        obtain ⟨lj, mj, gj, ej, cj, kj, pj, Pj⟩ := after_word w wj hw 12 hwjok
        obtain ⟨-, Wj, lWj, mWj, gWj⟩ := phase2_cell _ gj ej cj kj pj
        have hpj : ((applyList (eval w) wj).cp, (applyList (eval w) wj).ep) =
            pmul ((applyList (eval w) w0).cp, (applyList (eval w) w0).ep)
              (pmul (pinv (pActList idP w0)) (pActList idP wj)) := by
          rw [Pj, P0, pmul_assoc _ _ _ hbkj, hKj]
        rw [← hpj] at hk16
        exact fin wj Wj mj mWj gWj (by omega)

#print axioms upper_bound_28
