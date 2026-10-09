import CubeP.Kph1Thm
import CubeP.Phase34Proof
open Std

/-! Kociemba phase 1 in at most 12 moves, from the certified distance table over 2,217,093,120 cells. -/

theorem comp_parts : eoClosed = true ∧ coClosed = true ∧ mClosed = true ∧
    eoSet.contains eoZero = true ∧ coSet.contains St.id.co = true ∧ mSet.contains idE = true ∧
    tabOk eoL eIdx eoAct TE 2048 eoZero = true ∧ tabOk coL cIdx coAct TC 2187 St.id.co = true ∧
    tabOk mL sIdx maskAct TS 495 idE = true := by
  have h := compOk_true; unfold compOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j⟩

theorem closed_step {S : HashMap (Array Nat) Unit} {act : Array Nat → Nat → Array Nat}
    (hcl : S.toList.all (fun p => allMoves.all (fun m => S.contains (act p.1 m))) = true)
    {k : Array Nat} (hk : S.contains k = true) (m : Nat) (hm : m < 18) : S.contains (act k m) = true := by
  have := (List.all_eq_true.1 hcl) (k, ()) (mem_toList_of_contains hk)
  exact (List.all_eq_true.1 this) m (by simpa [allMoves] using hm)

def InC (x : St) : Prop := eoSet.contains x.eo = true ∧ coSet.contains x.co = true ∧ mSet.contains (maskOf x.ep) = true

theorem inC_apply {x : St} (hx : InC x) (m : Nat) (hm : m < 18) : InC (apply x m) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [apply_eo]; exact closed_step (by have := comp_parts.1; unfold eoClosed at this; exact this) h1 m hm
  · rw [apply_co]; exact closed_step (by have := comp_parts.2.1; unfold coClosed at this; exact this) h2 m hm
  · rw [apply_mask]; exact closed_step (by have := comp_parts.2.2.1; unfold mClosed at this; exact this) h3 m hm

theorem inC_applyList (w : List Nat) (hw : ∀ m ∈ w, m < 18) : ∀ x, InC x → InC (applyList x w) := by
  induction w with
  | nil => intro x hx; exact hx
  | cons h w ih =>
    intro x hx; rw [applyList_cons']
    exact ih (fun m hm => hw m (by simp [hm])) _ (inC_apply hx h (hw h (by simp)))

theorem inC_id : InC St.id := ⟨comp_parts.2.2.2.1, comp_parts.2.2.2.2.1, comp_parts.2.2.2.2.2.1⟩

theorem mem_L {S : HashMap (Array Nat) Unit} {k : Array Nat} (h : S.contains k = true) : k ∈ S.toList.map Prod.fst := by
  rw [List.mem_map]; exact ⟨(k, ()), mem_toList_of_contains h, rfl⟩

theorem tab_fact {l : List (Array Nat)} {idx : HashMap (Array Nat) Nat} {act : Array Nat → Nat → Array Nat}
    {t : Array Nat} {n : Nat} {k0 : Array Nat} (h : tabOk l idx act t n k0 = true) {k : Array Nat} (hk : k ∈ l) :
    ∃ r, idx[k]? = some r ∧ r < n ∧ (∀ m < 18, idx[act k m]? = some t[r * 18 + m]!) ∧ (r = idx[k0]! → k = k0) := by
  unfold tabOk at h; rw [Bool.and_eq_true] at h
  have h1 := (List.all_eq_true.1 h.1) k hk
  revert h1
  generalize idx[k]? = q
  intro h1
  cases q with
  | none => simp at h1
  | some r =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq,
      Bool.or_eq_true, bne_iff_ne, ne_eq] at h1
    refine ⟨r, rfl, h1.1.1, fun m hm => h1.1.2 m hm, fun hr => ?_⟩
    rcases h1.2 with h | h
    · exact absurd hr h
    · exact h

theorem bang_of {idx : HashMap (Array Nat) Nat} {k : Array Nat} {r : Nat} (h : idx[k]? = some r) : idx[k]! = r := by
  rw [HashMap.getElem!_eq_get!_getElem?, h]; rfl

theorem rank_apply (x : St) (hx : InC x) (m : Nat) (hm : m < 18) : rank (apply x m) = next (rank x) m := by
  obtain ⟨re, he, hre, hme, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.1 (mem_L hx.1)
  obtain ⟨rc, hc, hrc, hmc, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.1 (mem_L hx.2.1)
  obtain ⟨rs, hs, hrs, hms, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.2 (mem_L hx.2.2)
  have hr : rank x = (re * 2187 + rc) * 495 + rs := by
    unfold rank; rw [bang_of he, bang_of hc, bang_of hs]
  unfold rank next
  rw [apply_eo, apply_co, apply_mask, bang_of (hme m hm), bang_of (hmc m hm), bang_of (hms m hm)]
  rw [show eIdx[x.eo]! = re from bang_of he, show cIdx[x.co]! = rc from bang_of hc,
    show sIdx[maskOf x.ep]! = rs from bang_of hs]
  have e1 : ((re * 2187 + rc) * 495 + rs) / (2187 * 495) = re := by omega
  have e2 : ((re * 2187 + rc) * 495 + rs) / 495 % 2187 = rc := by omega
  have e3 : ((re * 2187 + rc) * 495 + rs) % 495 = rs := by omega
  rw [e1, e2, e3]

theorem rank_lt (x : St) (hx : InC x) : rank x < NN := by
  obtain ⟨re, he, hre, -, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.1 (mem_L hx.1)
  obtain ⟨rc, hc, hrc, -, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.1 (mem_L hx.2.1)
  obtain ⟨rs, hs, hrs, -, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.2 (mem_L hx.2.2)
  unfold rank NN; rw [bang_of he, bang_of hc, bang_of hs]; omega

theorem chkFrom_spec (d : ByteArray) : ∀ n, chkFrom d n = true → ∀ i < n, cellOk d i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    unfold chkFrom at h
    split at h
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact ih h i h'
      · subst h'; assumption
    · exact absurd h (by simp)

theorem anyMove_spec (d : ByteArray) (i v : Nat) : ∀ k, anyMove d i v k = true →
    ∃ m < k, (d.get! (next i m)).toNat + 1 = v := by
  intro k
  induction k with
  | zero => intro h; simp [anyMove] at h
  | succ k ih =>
    intro h
    unfold anyMove at h
    split at h
    · rename_i hc; exact ⟨k, by omega, by simpa using hc⟩
    · obtain ⟨m, hm, e⟩ := ih h; exact ⟨m, by omega, e⟩

theorem cell (i : Nat) (hi : i < NN) :
    ((distF ()).get! i).toNat ≤ 12 ∧ (((distF ()).get! i).toNat = 0 → i = i0) ∧
      (((distF ()).get! i).toNat ≠ 0 → ∃ m < 18, ((distF ()).get! (next i m)).toNat + 1 = ((distF ()).get! i).toNat) := by
  have h := chkFrom_spec _ _ (by have := kCheck_true; unfold kCheckF at this; exact this) i hi
  unfold cellOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun hz => ?_, fun hnz => ?_⟩
  · rcases h2 with h | h
    · exact absurd hz h
    · exact h
  · rcases h3 with h | h
    · exact absurd h hnz
    · exact anyMove_spec _ _ _ _ h

theorem descent : ∀ n x, InC x → ((distF ()).get! (rank x)).toNat = n →
    ∃ w : List Nat, w.length ≤ n ∧ (∀ m ∈ w, m < 18) ∧ rank (applyList x w) = i0 := by
  intro n
  induction n with
  | zero =>
    intro x hx hv
    exact ⟨[], by simp, by simp, (cell _ (rank_lt x hx)).2.1 hv⟩
  | succ n ih =>
    intro x hx hv
    obtain ⟨m, hm, e⟩ := (cell _ (rank_lt x hx)).2.2 (by omega)
    rw [← rank_apply x hx m hm] at e
    obtain ⟨w, hl, hw, hr⟩ := ih (apply x m) (inC_apply hx m hm) (by omega)
    refine ⟨m :: w, by simp only [List.length_cons]; omega, ?_, by rw [applyList_cons']; exact hr⟩
    intro k hk; simp at hk; rcases hk with rfl | hk
    · exact hm
    · exact hw k hk

theorem rank_eq_i0 (y : St) (hy : InC y) (h : rank y = i0) :
    y.eo = eoZero ∧ y.co = St.id.co ∧ maskOf y.ep = idE := by
  obtain ⟨re, he, hre, -, ie⟩ := tab_fact comp_parts.2.2.2.2.2.2.1 (mem_L hy.1)
  obtain ⟨rc, hc, hrc, -, ic⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.1 (mem_L hy.2.1)
  obtain ⟨rs, hs, hrs, -, is⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.2 (mem_L hy.2.2)
  obtain ⟨re0, he0, hre0, -, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.1 (mem_L comp_parts.2.2.2.1)
  obtain ⟨rc0, hc0, hrc0, -, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.1 (mem_L comp_parts.2.2.2.2.1)
  obtain ⟨rs0, hs0, hrs0, -, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.2 (mem_L comp_parts.2.2.2.2.2.1)
  unfold rank i0 at h
  rw [bang_of he, bang_of hc, bang_of hs, bang_of he0, bang_of hc0, bang_of hs0] at h
  refine ⟨ie ?_, ic ?_, is ?_⟩
  · rw [bang_of he0]; omega
  · rw [bang_of hc0]; omega
  · rw [bang_of hs0]; omega

/-- **Kociemba phase 1:** every reachable position is brought into <U,D,R2,L2,F2,B2>-form (edges and corners
oriented, E-slice edges in the E slice) by at most 12 face turns. -/
theorem kociemba_phase1 (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∃ w', w'.length ≤ 12 ∧ (∀ m ∈ w', m < 18) ∧ (applyList (eval w) w').eo = eoZero ∧
      (applyList (eval w) w').co = St.id.co ∧ maskOf (applyList (eval w) w').ep = idE := by
  have hx : InC (eval w) := inC_applyList w hw St.id inC_id
  obtain ⟨w', hl, hw', hr⟩ := descent _ (eval w) hx rfl
  have hle := (cell _ (rank_lt _ hx)).1
  exact ⟨w', by omega, hw', rank_eq_i0 _ (inC_applyList w' hw' _ hx) hr⟩

#print axioms kociemba_phase1
