import CubeP.Final40
import CubeP.Kph2Thm
open Std

/-! Kociemba's phase 2 in at most 18 moves, and the 30-move bound. -/

theorem facts_all : (idxOkC () = true ∧ idxOkE () = true ∧ listInC () = true ∧ listInE () = true ∧ closedC () = true ∧
    closedE () = true ∧ symOk () = true ∧ mvOkC () = true ∧ mvOkE () = true ∧ compatC () = true ∧ compatE () = true ∧
    invOk () = true ∧ idOk () = true ∧ parOk () = true ∧ startOk () = true) ∧ stabOk () = true ∧ canonOk () = true ∧ idSymOk () = true := by
  have h := factsOk_true; unfold factsOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, h1⟩, i⟩, j⟩, k⟩, l⟩, m⟩, n⟩, o⟩, p1⟩, q1⟩, r1⟩ := h
  exact ⟨⟨a, b, c, d, e, f, g, h1, i, j, k, l, m, n, o⟩, p1, q1, r1⟩
theorem facts : idxOkC () = true ∧ idxOkE () = true ∧ listInC () = true ∧ listInE () = true ∧ closedC () = true ∧
    closedE () = true ∧ symOk () = true ∧ mvOkC () = true ∧ mvOkE () = true ∧ compatC () = true ∧ compatE () = true ∧
    invOk () = true ∧ idOk () = true ∧ parOk () = true ∧ startOk () = true := facts_all.1

theorem lt_of_range_all {f : Nat → Bool} {n i : Nat} (h : (List.range n).all f = true) (hi : i < n) : f i = true :=
  (List.all_eq_true.1 h) i (List.mem_range.2 hi)

theorem idxC {k : Array Nat} (h : cpG.contains k = true) : ∃ r, cpGI[k]? = some r ∧ r < NCP ∧ cpGL[r]! = k := by
  have := (List.all_eq_true.1 facts.1) (k, ()) (mem_toList_of_contains h)
  dsimp only at this
  revert this; generalize cpGI[k]? = q; intro this
  cases q with
  | none => simp at this
  | some r =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨r, rfl, this.1, this.2⟩

theorem idxE {k : Array Nat} (h : epG.contains k = true) : ∃ r, epGI[k]? = some r ∧ r < NE ∧ epGL[r]! = k := by
  have := (List.all_eq_true.1 facts.2.1) (k, ()) (mem_toList_of_contains h)
  dsimp only at this
  revert this; generalize epGI[k]? = q; intro this
  cases q with
  | none => simp at this
  | some r =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨r, rfl, this.1, this.2⟩

theorem cpGL_in {r : Nat} (hr : r < NCP) : cpG.contains cpGL[r]! = true := lt_of_range_all facts.2.2.1 hr
theorem epGL_in {e : Nat} (he : e < NE) : epG.contains epGL[e]! = true := lt_of_range_all facts.2.2.2.1 he

theorem closedC_parts {k : Array Nat} (h : cpG.contains k = true) :
    (∀ m ∈ g2Moves, cpG.contains (cpAct k m) = true) ∧ (∀ s < 16, cpG.contains (conjC s k) = true) := by
  have := (List.all_eq_true.1 facts.2.2.2.2.1) (k, ()) (mem_toList_of_contains h)
  simp only [Bool.and_eq_true] at this
  exact ⟨List.all_eq_true.1 this.1, fun s hs => lt_of_range_all this.2 hs⟩

theorem closedE_parts {k : Array Nat} (h : epG.contains k = true) :
    (∀ m ∈ g2Moves, epG.contains (epAct k m) = true) ∧ (∀ s < 16, epG.contains (conjE s k) = true) := by
  have := (List.all_eq_true.1 facts.2.2.2.2.2.1) (k, ()) (mem_toList_of_contains h)
  simp only [Bool.and_eq_true] at this
  exact ⟨List.all_eq_true.1 this.1, fun s hs => lt_of_range_all this.2 hs⟩

theorem sym_at {r : Nat} (hr : r < NCP) :
    clsT[r]! < NC ∧ syT[r]! < 16 ∧ conjC syT[r]! cpGL[r]! = cpGL[repsT[clsT[r]!]!]! := by
  have h := facts.2.2.2.2.2.2.1; unfold symOk at h; rw [Bool.and_eq_true] at h
  have := lt_of_range_all h.1 hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem reps_lt {c : Nat} (hc : c < NC) : repsT[c]! < NCP := by
  have h := facts.2.2.2.2.2.2.1; unfold symOk at h; rw [Bool.and_eq_true] at h
  exact of_decide_eq_true (lt_of_range_all h.2 hc)

theorem mvC {r j : Nat} (hr : r < NCP) (hj : j < 10) : cpMv[r * 10 + j]! = cpGI[cpAct cpGL[r]! g2A[j]!]! := by
  have := lt_of_range_all (lt_of_range_all facts.2.2.2.2.2.2.2.1 hr) hj
  simpa using this

theorem mvE {e j s : Nat} (he : e < NE) (hj : j < 10) (hs : s < 16) :
    epMv[e * 10 + j]! = epGI[epAct epGL[e]! g2A[j]!]! ∧ epCj[e * 16 + s]! = epGI[conjE s epGL[e]!]! := by
  have := lt_of_range_all facts.2.2.2.2.2.2.2.2.1 he
  simp only [Bool.and_eq_true] at this
  exact ⟨by simpa using lt_of_range_all this.1 hj, by simpa using lt_of_range_all this.2 hs⟩

theorem compC {k : Array Nat} (h : cpG.contains k = true) {s : Nat} (hs : s < 16) {m : Nat} (hm : m ∈ g2Moves) :
    conjC s (cpAct k m) = cpAct (conjC s k) (mu s m) ∧ mu s m ∈ g2Moves := by
  have := (List.all_eq_true.1 facts.2.2.2.2.2.2.2.2.2.1) (k, ()) (mem_toList_of_contains h)
  have := (List.all_eq_true.1 (lt_of_range_all this hs)) m hm
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1, List.contains_iff_mem.1 this.2⟩

theorem compE {k : Array Nat} (h : epG.contains k = true) {s : Nat} (hs : s < 16) {m : Nat} (hm : m ∈ g2Moves) :
    conjE s (epAct k m) = epAct (conjE s k) (mu s m) := by
  have := (List.all_eq_true.1 facts.2.2.2.2.2.2.2.2.2.2.1) (k, ()) (mem_toList_of_contains h)
  have := (List.all_eq_true.1 (lt_of_range_all this hs)) m hm
  simpa using this

theorem inv_parts : (∀ s < 16, invS[s]! < 16) ∧
    (∀ k, cpG.contains k = true → ∀ s < 16, conjC invS[s]! (conjC s k) = k) ∧
    (∀ k, epG.contains k = true → ∀ s < 16, conjE invS[s]! (conjE s k) = k) := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.1; unfold invOk at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun s hs => of_decide_eq_true (lt_of_range_all h.1.1 hs), fun k hk s hs => ?_, fun k hk s hs => ?_⟩
  · have := lt_of_range_all ((List.all_eq_true.1 h.1.2) (k, ()) (mem_toList_of_contains hk)) hs
    simpa using this
  · have := lt_of_range_all ((List.all_eq_true.1 h.2) (k, ()) (mem_toList_of_contains hk)) hs
    simpa using this

theorem id_parts : (∀ s < 16, conjC s St.id.cp = St.id.cp ∧ conjE s St.id.ep = St.id.ep) ∧ stateOf idCell = idP := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.1; unfold idOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨fun s hs => ?_, h.2⟩
  have := lt_of_range_all h.1 hs
  simpa using this

theorem par_parts : (∀ k, cpG.contains k = true → ∀ s < 16, inv (conjC s k).toList % 2 = inv k.toList % 2) ∧
    (∀ k, epG.contains k = true → ∀ s < 16, inv (conjE s k).toList % 2 = inv k.toList % 2) ∧
    (∀ c < NC, pcT[c]! = inv cpGL[repsT[c]!]!.toList % 2) ∧ (∀ e < NE, peT[e]! = inv epGL[e]!.toList % 2) := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1; unfold parOk at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun k hk s hs => ?_, fun k hk s hs => ?_, fun c hc => ?_, fun e he => ?_⟩
  · simpa using lt_of_range_all ((List.all_eq_true.1 h.1.1.1) (k, ()) (mem_toList_of_contains hk)) hs
  · simpa using lt_of_range_all ((List.all_eq_true.1 h.1.1.2) (k, ()) (mem_toList_of_contains hk)) hs
  · simpa using lt_of_range_all h.1.2 hc
  · simpa using lt_of_range_all h.2 he

theorem g2A_mem : ∀ j < 10, g2A[j]! ∈ g2Moves := by decide

-- domain and conjugation
def Dom (p : P) : Prop := cpG.contains p.1 = true ∧ epG.contains p.2 = true

theorem dom_act {p : P} (hp : Dom p) {m : Nat} (hm : m ∈ g2Moves) : Dom (pAct p m) :=
  ⟨(closedC_parts hp.1).1 m hm, (closedE_parts hp.2).1 m hm⟩
theorem dom_conj {p : P} (hp : Dom p) {s : Nat} (hs : s < 16) : Dom (conjP s p) :=
  ⟨(closedC_parts hp.1).2 s hs, (closedE_parts hp.2).2 s hs⟩

theorem conj_act {p : P} (hp : Dom p) {s : Nat} (hs : s < 16) {m : Nat} (hm : m ∈ g2Moves) :
    conjP s (pAct p m) = pAct (conjP s p) (mu s m) := by
  show (conjC s (cpAct p.1 m), conjE s (epAct p.2 m)) = (cpAct (conjC s p.1) (mu s m), epAct (conjE s p.2) (mu s m))
  rw [(compC hp.1 hs hm).1, compE hp.2 hs hm]

theorem pActList_cons (p : P) (a : Nat) (W : List Nat) : pActList p (a :: W) = pActList (pAct p a) W := rfl

theorem conj_list {t : Nat} (ht : t < 16) : ∀ W : List Nat, (∀ m ∈ W, m ∈ g2Moves) → ∀ q, Dom q →
    pActList (conjP t q) (W.map (mu t)) = conjP t (pActList q W) := by
  intro W
  induction W with
  | nil => intro _ q _; rfl
  | cons m W ih =>
    intro hw q hq
    have hm : m ∈ g2Moves := hw m (by simp)
    rw [List.map_cons, pActList_cons, pActList_cons, ← conj_act hq ht hm]
    exact ih (fun m' hm' => hw m' (by simp [hm'])) _ (dom_act hq hm)

theorem mu_mem {t : Nat} (ht : t < 16) (W : List Nat) (hw : ∀ m ∈ W, m ∈ g2Moves) : ∀ m ∈ W.map (mu t), m ∈ g2Moves := by
  intro m hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
  exact (compC (cpGL_in (r := 0) (by decide)) ht (hw a ha)).2

theorem conj_inv {p : P} (hp : Dom p) {s : Nat} (hs : s < 16) : conjP invS[s]! (conjP s p) = p := by
  have h1 := inv_parts.2.1 _ hp.1 s hs
  have h2 := inv_parts.2.2 _ hp.2 s hs
  unfold conjP
  simp only [h1, h2]

theorem conj_idP {t : Nat} (ht : t < 16) : conjP t idP = idP := by
  have h1 := (id_parts.1 t ht).1
  have h2 := (id_parts.1 t ht).2
  unfold conjP idP
  simp only [h1, h2]

-- cells
theorem NE_pos : 0 < NE := by decide

theorem canon_cases (c e : Nat) : canon c e = e ∨ ∃ t ∈ stabT[c]!, canon c e = epCj[e * 16 + t]! := by
  unfold canon
  generalize stabT[c]! = L
  suffices H : ∀ a, L.foldl (fun a t => min a epCj[e * 16 + t]!) a = a ∨
      ∃ t ∈ L, L.foldl (fun a t => min a epCj[e * 16 + t]!) a = epCj[e * 16 + t]! by
    exact H e
  induction L with
  | nil => intro a; left; rfl
  | cons t L ih =>
    intro a
    simp only [List.foldl_cons]
    rcases ih (min a epCj[e * 16 + t]!) with h | ⟨t', ht', h⟩
    · rw [h]
      by_cases hle : a ≤ epCj[e * 16 + t]!
      · left; exact Nat.min_eq_left hle
      · right; exact ⟨t, by simp, Nat.min_eq_right (by omega)⟩
    · right; exact ⟨t', by simp [ht'], h⟩

theorem stab_at {c t : Nat} (hc : c < NC) (ht : t ∈ stabT[c]!) : t < 16 ∧ conjC t cpGL[repsT[c]!]! = cpGL[repsT[c]!]! := by
  have := (List.all_eq_true.1 (lt_of_range_all facts_all.2.1 hc)) t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact this

theorem canon_idem {c e : Nat} (hc : c < NC) (he : e < NE) : canon c (canon c e) = canon c e := by
  have h := lt_of_range_all facts_all.2.2.1 hc
  by_cases hs : (stabT[c]!).isEmpty = true
  · have hn : stabT[c]! = [] := List.isEmpty_iff.1 hs
    unfold canon; rw [hn]; rfl
  · rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd h hs
    · simpa using lt_of_range_all h he

theorem idSym_C {k : Array Nat} (h : cpG.contains k = true) : conjC 0 k = k := by
  have h1 := facts_all.2.2.2; unfold idSymOk at h1; rw [Bool.and_eq_true] at h1
  simpa using (List.all_eq_true.1 h1.1) (k, ()) (mem_toList_of_contains h)
theorem idSym_E {k : Array Nat} (h : epG.contains k = true) : conjE 0 k = k := by
  have h1 := facts_all.2.2.2; unfold idSymOk at h1; rw [Bool.and_eq_true] at h1
  simpa using (List.all_eq_true.1 h1.2) (k, ()) (mem_toList_of_contains h)

theorem cell_facts {p : P} (hp : Dom p) : ∃ c e σ t, c < NC ∧ e < NE ∧ σ < 16 ∧ t < 16 ∧
    cellOf p = c * NE + e ∧ canon c e = e ∧ stateOf (cellOf p) = conjP t (conjP σ p) ∧
    cpGL[repsT[c]!]! = conjC t (conjC σ p.1) ∧ epGL[e]! = conjE t (conjE σ p.2) := by
  obtain ⟨r, hr, hrl, hrk⟩ := idxC hp.1
  obtain ⟨hcl, hsy, hconj⟩ := sym_at hrl
  have hqc : cpG.contains (conjC syT[r]! p.1) = true := (closedC_parts hp.1).2 _ hsy
  have hq : epG.contains (conjE syT[r]! p.2) = true := (closedE_parts hp.2).2 _ hsy
  obtain ⟨e0, he0, he0l, he0k⟩ := idxE hq
  have hc1 : cpGL[repsT[clsT[r]!]!]! = conjC syT[r]! p.1 := by rw [← hconj, hrk]
  -- the canonical index and its witness symmetry
  have hex : ∃ t, t < 16 ∧ canon clsT[r]! e0 < NE ∧ cpGL[repsT[clsT[r]!]!]! = conjC t (conjC syT[r]! p.1) ∧
      epGL[canon clsT[r]! e0]! = conjE t (conjE syT[r]! p.2) := by
    rcases canon_cases clsT[r]! e0 with h | ⟨t, ht, h⟩
    · refine ⟨0, by decide, by rw [h]; exact he0l, by rw [hc1, idSym_C hqc], by rw [h, he0k, idSym_E hq]⟩
    · obtain ⟨ht16, hst⟩ := stab_at hcl ht
      have hq2 : epG.contains (conjE t (conjE syT[r]! p.2)) = true := (closedE_parts hq).2 _ ht16
      obtain ⟨e1, he1, he1l, he1k⟩ := idxE hq2
      have hce : canon clsT[r]! e0 = e1 := by
        rw [h, (mvE he0l (j := 0) (by decide) ht16).2, he0k, bang_of he1]
      refine ⟨t, ht16, by rw [hce]; exact he1l, by rw [← hst, hc1], by rw [hce, he1k]⟩
  obtain ⟨t, ht, hcl', hcp, hep⟩ := hex
  have hcell : cellOf p = clsT[r]! * NE + canon clsT[r]! e0 := by
    unfold cellOf; dsimp only; rw [bang_of hr, bang_of he0]
  refine ⟨clsT[r]!, canon clsT[r]! e0, syT[r]!, t, hcl, hcl', hsy, ht, hcell, canon_idem hcl he0l, ?_, hcp, hep⟩
  rw [hcell]
  unfold stateOf
  have h1 : (clsT[r]! * NE + canon clsT[r]! e0) / NE = clsT[r]! := by unfold NE at *; omega
  have h2 : (clsT[r]! * NE + canon clsT[r]! e0) % NE = canon clsT[r]! e0 := by unfold NE at *; omega
  rw [h1, h2, hcp, hep]; rfl

theorem nextC_eq {c e j : Nat} (hc : c < NC) (he : e < NE) (hj : j < 10) :
    nextC (c * NE + e) j = cellOf (pAct (stateOf (c * NE + e)) g2A[j]!) := by
  have h1 : (c * NE + e) / NE = c := by unfold NE at *; omega
  have h2 : (c * NE + e) % NE = e := by unfold NE at *; omega
  have hrc := reps_lt hc
  have hg := g2A_mem j hj
  have hk : cpG.contains (cpAct cpGL[repsT[c]!]! g2A[j]!) = true := (closedC_parts (cpGL_in hrc)).1 _ hg
  obtain ⟨r', hr', hr'l, -⟩ := idxC hk
  have hke : epG.contains (epAct epGL[e]! g2A[j]!) = true := (closedE_parts (epGL_in he)).1 _ hg
  obtain ⟨e1, he1, he1l, he1k⟩ := idxE hke
  obtain ⟨-, hsy, -⟩ := sym_at hr'l
  have hm1 : cpMv[repsT[c]! * 10 + j]! = r' := by rw [mvC hrc hj, bang_of hr']
  have hm2 : epMv[e * 10 + j]! = e1 := by rw [(mvE he hj (s := 0) (by decide)).1, bang_of he1]
  have hm3 : epCj[e1 * 16 + syT[r']!]! = epGI[conjE syT[r']! (epAct epGL[e]! g2A[j]!)]! := by
    rw [(mvE he1l (j := 0) (by decide) hsy).2, he1k]
  unfold nextC cellOf stateOf pAct
  simp only [h1, h2, hm1, hm2, hm3, bang_of hr']

theorem chk2From_succ (d : ByteArray) (n : Nat) :
    chk2From d (n + 1) = if cell2Ok d n then chk2From d n else false := rfl
theorem anyMove2_zero (d : ByteArray) (i v : Nat) : anyMove2 d i v 0 = false := rfl
theorem anyMove2_succ (d : ByteArray) (i v k : Nat) : anyMove2 d i v (k + 1) =
    if (d.get! (nextC i k)).toNat + 1 == v && parC (nextC i k) == 0 then true else anyMove2 d i v k := rfl

theorem chk2From_spec (d : ByteArray) : ∀ n, chk2From d n = true → ∀ i < n, cell2Ok d i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    rw [chk2From_succ] at h
    by_cases hc : cell2Ok d n = true
    · rw [if_pos hc] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact ih h i h'
      · rw [h']; exact hc
    · rw [if_neg hc] at h; exact absurd h (by simp)

theorem anyMove2_spec (d : ByteArray) (i v : Nat) : ∀ k, anyMove2 d i v k = true →
    ∃ j < k, (d.get! (nextC i j)).toNat + 1 = v ∧ parC (nextC i j) = 0 := by
  intro k
  induction k with
  | zero => intro h; rw [anyMove2_zero] at h; exact absurd h (by simp)
  | succ k ih =>
    intro h
    rw [anyMove2_succ] at h
    by_cases hc : ((d.get! (nextC i k)).toNat + 1 == v && parC (nextC i k) == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨k, by omega, hc.1, hc.2⟩
    · rw [if_neg hc] at h
      obtain ⟨j, hj, e⟩ := ih h; exact ⟨j, by omega, e⟩

theorem cell2 (i : Nat) (hi : i < N2) (hpar : parC i = 0) (hcan : canon (i / NE) (i % NE) = i % NE) :
    ((dist2F ()).get! i).toNat ≤ 18 ∧ (((dist2F ()).get! i).toNat = 0 → i = idCell) ∧
      (((dist2F ()).get! i).toNat ≠ 0 → ∃ j < 10, ((dist2F ()).get! (nextC i j)).toNat + 1 = ((dist2F ()).get! i).toNat ∧
        parC (nextC i j) = 0) := by
  have h := chk2From_spec _ _ (by have := k2Check2_true; unfold k2CheckF2 at this; exact this) i hi
  unfold cell2Ok at h
  simp only [hpar, hcan, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun hz => ?_, fun hnz => ?_⟩
  · rcases h2 with h | h
    · exact absurd hz h
    · exact h
  · rcases h3 with h | h
    · exact absurd h hnz
    · exact anyMove2_spec _ _ _ _ h

theorem cellOf_can {p : P} (hp : Dom p) : cellOf p < N2 ∧ canon (cellOf p / NE) (cellOf p % NE) = cellOf p % NE := by
  obtain ⟨c, e, σ, t, hc, he, hσ, ht, hcell, hcan, -, -, -⟩ := cell_facts hp
  have h1 : (c * NE + e) / NE = c := by unfold NE at *; omega
  have h2 : (c * NE + e) % NE = e := by unfold NE at *; omega
  rw [hcell, h1, h2]
  exact ⟨by unfold N2 NE NC at *; omega, hcan⟩

theorem g2_descent : ∀ n p, Dom p → parC (cellOf p) = 0 → ((dist2F ()).get! (cellOf p)).toNat = n →
    ∃ W : List Nat, W.length ≤ n ∧ (∀ m ∈ W, m ∈ g2Moves) ∧ pActList p W = idP := by
  intro n
  induction n with
  | zero =>
    intro p hp hpar hv
    obtain ⟨c, e, σ, t, hc, he, hσ, ht, hcell, -, hst, -, -⟩ := cell_facts hp
    obtain ⟨hlt, hcan⟩ := cellOf_can hp
    have h0 := (cell2 _ hlt hpar hcan).2.1 hv
    have hq : conjP t (conjP σ p) = idP := by rw [← hst, h0]; exact id_parts.2
    have hd1 : Dom (conjP σ p) := dom_conj hp hσ
    have hpe : p = idP := by
      rw [← conj_inv hp hσ, ← conj_inv hd1 ht, hq, conj_idP (inv_parts.1 t ht), conj_idP (inv_parts.1 σ hσ)]
    exact ⟨[], by simp, by simp, by rw [hpe]; rfl⟩
  | succ n ih =>
    intro p hp hpar hv
    obtain ⟨c, e, σ, t, hc, he, hσ, ht, hcell, -, hst, -, -⟩ := cell_facts hp
    obtain ⟨hlt, hcan⟩ := cellOf_can hp
    obtain ⟨j, hj, hd, hpj⟩ := (cell2 _ hlt hpar hcan).2.2 (by omega)
    have hd1 : Dom (conjP σ p) := dom_conj hp hσ
    have hqd : Dom (conjP t (conjP σ p)) := dom_conj hd1 ht
    have hg := g2A_mem j hj
    have hyd : Dom (pAct (conjP t (conjP σ p)) g2A[j]!) := dom_act hqd hg
    have hn : nextC (cellOf p) j = cellOf (pAct (conjP t (conjP σ p)) g2A[j]!) := by
      rw [hcell, nextC_eq hc he hj, ← hcell, hst]
    rw [hn] at hd hpj
    obtain ⟨W, hl, hw, hy⟩ := ih _ hyd hpj (by omega)
    have hσi := inv_parts.1 σ hσ
    have hti := inv_parts.1 t ht
    have hw' : ∀ m ∈ g2A[j]! :: W, m ∈ g2Moves := by
      intro m hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm
      · exact hg
      · exact hw m hm
    have hw'' := mu_mem hti _ hw'
    refine ⟨((g2A[j]! :: W).map (mu invS[t]!)).map (mu invS[σ]!), by simp; omega, mu_mem hσi _ hw'', ?_⟩
    have hp' : p = conjP invS[σ]! (conjP invS[t]! (conjP t (conjP σ p))) := by
      rw [conj_inv hd1 ht, conj_inv hp hσ]
    rw [hp', conj_list hσi _ hw'' _ (dom_conj hqd hti), conj_list hti _ hw' _ hqd, pActList_cons, hy,
      conj_idP hti, conj_idP hσi]

theorem applyList_pact (W : List Nat) : ∀ x : St,
    ((applyList x W).cp, (applyList x W).ep) = pActList (x.cp, x.ep) W := by
  induction W with
  | nil => intro x; rfl
  | cons m W ih =>
    intro x
    rw [applyList_cons', pActList_cons]
    have : pAct (x.cp, x.ep) m = ((apply x m).cp, (apply x m).ep) := rfl
    rw [this]; exact ih _

theorem ep_slice (x : St) (hg : Good x) (hE : maskOf x.ep = idE) :
    ∀ i (h1 : i < x.ep.toList.length) (h2 : i < sliceSets2.length), x.ep.toList[i] ∈ sliceSets2[i] := by
  intro i h1 h2
  have hi12 : i < 12 := by simpa [sliceSets2] using h2
  have hsz : x.ep.size = 12 := hg.2.1
  have hmem : x.ep.toList[i] ∈ List.range 12 := hg.2.2.2.1.mem_iff.1 (List.getElem_mem h1)
  have he : x.ep.toList[i] < 12 := List.mem_range.1 hmem
  have hx : x.ep[i]! = x.ep.toList[i] := by
    rw [getElem!_pos x.ep i (by omega), Array.getElem_toList]
  have hc1 : cls x.ep.toList[i] = idE[i]! := by
    rw [← hx, ← hE]; exact (getElem!_map_cls x.ep i).symm
  have hs := facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2; unfold startOk at hs
  simp only [Bool.and_eq_true] at hs
  have h3 := List.all_eq_true.1 ((List.all_eq_true.1 hs.2) i (List.mem_range.2 hi12)) _ (List.mem_range.2 he)
  rw [← hc1] at h3
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or] at h3
  rw [getElem!_pos sliceSets2 i h2] at h3
  exact List.contains_iff_mem.1 h3

/-- **Kociemba phase 2:** every domino-reduced position (edges and corners oriented, E-slice edges in the E slice)
is solved by at most 18 moves of <U,D,R2,L2,F2,B2>. -/
theorem kociemba_phase2 (x : St) (hg : Good x) (heo : x.eo = eoZero) (hco : x.co = St.id.co)
    (hmk : maskOf x.ep = idE) (hcp : cpSet.contains x.cp = true) :
    ∃ W, W.length ≤ 18 ∧ (∀ m ∈ W, m ∈ g2Moves) ∧ applyList x W = St.id := by
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
  obtain ⟨c, e, σ, t, hc, he, hσ, ht, hcell, -, -, hcr, her⟩ := cell_facts hp
  obtain ⟨hlt, hcan⟩ := cellOf_can hp
  have hpar : parC (cellOf (x.cp, x.ep)) = 0 := by
    rw [hcell]; unfold parC
    have h1 : (c * NE + e) / NE = c := by unfold NE at *; omega
    have h2 : (c * NE + e) % NE = e := by unfold NE at *; omega
    have hdc' : cpG.contains (conjC σ x.cp) = true := (closedC_parts hdc).2 _ hσ
    have hde' : epG.contains (conjE σ x.ep) = true := (closedE_parts hde).2 _ hσ
    rw [h1, h2, par_parts.2.2.1 c hc, par_parts.2.2.2 e he, hcr, her,
      par_parts.1 _ hdc' t ht, par_parts.2.1 _ hde' t ht,
      par_parts.1 _ hdc σ hσ, par_parts.2.1 _ hde σ hσ]
    have := hg.2.2.2.2; omega
  have hv := (cell2 _ hlt hpar hcan).1
  obtain ⟨W, hl, hw, hpw⟩ := g2_descent _ _ hp hpar rfl
  refine ⟨W, by omega, hw, ?_⟩
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

#print axioms kociemba_phase2

/-- **30-move bound**, formally: Kociemba's phase 1 (≤ 12) then phase 2 (≤ 18). Every position reachable with
face turns is solved by at most 30 face turns. -/
theorem upper_bound_30 (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∃ W : List Nat, W.length ≤ 30 ∧ (∀ m ∈ W, m < 18) ∧ applyList (eval w) W = St.id := by
  obtain ⟨w1, l1, m1, e1, c1, k1⟩ := kociemba_phase1 w hw
  rw [← eval_append] at e1 c1 k1
  have hu1 := all_append hw m1
  obtain ⟨W2, l2, m2, g⟩ := kociemba_phase2 (eval (w ++ w1)) (parity_law _ hu1) e1 c1 k1
    (cp_reach _ hu1 St.id cpId_true)
  have m2' : ∀ m ∈ W2, m < 18 := fun m hm => g2_lt (m2 m hm)
  refine ⟨w1 ++ W2, by simp only [List.length_append]; omega, all_append m1 m2', ?_⟩
  rw [applyList_append, ← eval_append]; exact g

#print axioms upper_bound_30
