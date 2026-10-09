import CubeP.LowerTThm
import CubeP.Phase34Proof
import CubeP.Phase4Thm
open Std

/-! Each Thistlethwaite phase bound (7, 10, 13; and 15 for phase 4, `square_group_gods_number`) is attained. -/

theorem mem_of_some {K : Type} [BEq K] [Hashable K] [LawfulBEq K] {t : HashMap K (Option (List Nat))} {k : K}
    (h : t.contains k = true) : ∃ o, (k, o) ∈ t.toList := by
  rw [HashMap.contains_eq_isSome_getElem?] at h
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
  exact ⟨o, (HashMap.mem_toList_iff_getElem?_eq_some).2 ho⟩

-- phase 1
theorem p1_parts : eoTable.toList.all (fun p => allMoves.all (fun m => decide (dOf eoTable p.1 ≤ dOf eoTable (eoAct p.1 m) + 1))) = true ∧
    dOf eoTable eoZero = 0 ∧ dOf eoTable (eval superflip).eo = 7 ∧ superflip.all (fun m => decide (m < 18)) = true := by
  have h := p1Low_true; unfold p1LowOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem p1_reach (w : List Nat) (hw : ∀ m ∈ w, m < 18) : ∀ x : St, eoTable.contains x.eo = true →
    dOf eoTable x.eo ≤ dOf eoTable (applyList x w).eo + w.length := by
  induction w with
  | nil => intro x _; simp [applyList]
  | cons h w ih =>
    intro x hx
    have hm : h < 18 := hw h (by simp)
    obtain ⟨o, ho⟩ := mem_of_some hx
    have hl := of_decide_eq_true ((List.all_eq_true.1 ((List.all_eq_true.1 p1_parts.1) _ ho)) h (by simpa [allMoves] using hm))
    obtain ⟨o', ho'⟩ := eo_some hx
    obtain ⟨-, -, -, -, -, hcl⟩ := eo_entry ho'
    have hc : eoTable.contains (apply x h).eo = true := by rw [apply_eo]; exact hcl h (by simpa [allMoves] using hm)
    have := ih (fun m hm => hw m (by simp [hm])) (apply x h) hc
    rw [applyList_cons']; rw [apply_eo] at this
    simp only [List.length_cons]; simp only at hl; omega

/-- **Thistlethwaite phase 1 needs 7 moves:** the superflip cannot have its edges oriented in fewer than 7 turns. -/
theorem thistle_phase1_lower (w : List Nat) (hw : ∀ m ∈ w, m < 18)
    (h : (applyList (eval superflip) w).eo = eoZero) : 7 ≤ w.length := by
  have hs : ∀ m ∈ superflip, m < 18 := fun m hm => of_decide_eq_true ((List.all_eq_true.1 p1_parts.2.2.2) m hm)
  have hx : eoTable.contains (eval superflip).eo = true := eo_reach superflip hs St.id eo_parts.2
  have := p1_reach w hw _ hx
  rw [h, p1_parts.2.1, p1_parts.2.2.1] at this
  omega

-- phase 2
theorem p2_parts : (k2TableF ()).toList.all (fun p => g1Moves.all (fun m =>
      decide (dOf (k2TableF ()) p.1 ≤ dOf (k2TableF ()) (k2Act p.1 m) + 1))) = true ∧
    dOf (k2TableF ()) k2Start = 0 ∧ dOf (k2TableF ()) (key2 (eval wit2)) = 10 ∧
    wit2.all (fun m => decide (m < 18)) = true ∧ (eval wit2).eo = eoZero := by
  have h := p2Low_true; unfold p2LowF p2LowW at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem p2_reach (w : List Nat) (hw : ∀ m ∈ w, m ∈ g1Moves) : ∀ x : St, (k2TableF ()).contains (key2 x) = true →
    dOf (k2TableF ()) (key2 x) ≤ dOf (k2TableF ()) (key2 (applyList x w)) + w.length := by
  induction w with
  | nil => intro x _; simp [applyList]
  | cons h w ih =>
    intro x hx
    have hg : h ∈ g1Moves := hw h (by simp)
    have hm : h < 18 := by simp [g1Moves] at hg; omega
    obtain ⟨o, ho⟩ := mem_of_some hx
    have hl := of_decide_eq_true ((List.all_eq_true.1 ((List.all_eq_true.1 p2_parts.1) _ ho)) h hg)
    obtain ⟨o', ho'⟩ := k2_some hx
    obtain ⟨-, -, -, -, -, hcl⟩ := k2_entry ho'
    have hc : (k2TableF ()).contains (key2 (apply x h)) = true := by
      rw [apply_key2]; exact hcl h (by simpa [allMoves] using hm)
    have := ih (fun m hm => hw m (by simp [hm])) (apply x h) hc
    rw [applyList_cons']; rw [apply_key2] at this
    simp only [List.length_cons]; simp only at hl; omega

/-- **Thistlethwaite phase 2 needs 10 moves:** from `wit2` (edges oriented), no word in <U,D,R,L,F2,B2> of fewer
than 10 moves orients the corners and places the E-slice edges. -/
theorem thistle_phase2_lower (w : List Nat) (hw : ∀ m ∈ w, m ∈ g1Moves)
    (h : key2 (applyList (eval wit2) w) = key2 St.id) : 10 ≤ w.length := by
  have hs : ∀ m ∈ wit2, m < 18 := fun m hm => of_decide_eq_true ((List.all_eq_true.1 p2_parts.2.2.2.1) m hm)
  have hx : (k2TableF ()).contains (key2 (eval wit2)) = true :=
    k2_reach wit2 hs St.id (by rw [key2_start]; exact k2_parts.2)
  have := p2_reach w hw _ hx
  rw [h, key2_start, p2_parts.2.1, p2_parts.2.2.1] at this
  omega

-- phase 3
theorem p3_parts : cpSet.toList.all (fun p => ms70.all (fun k => g2Moves.all (fun m =>
      decide (dOf (k3TableF ()) (p.1, k) ≤ dOf (k3TableF ()) (k3Act (p.1, k) m) + 1)))) = true ∧
    hList.all (fun c => dOf (k3TableF ()) (c, idMS) == 0) = true ∧
    dOf (k3TableF ()) (key3 (eval wit3)) = 13 ∧ wit3.all (fun m => decide (m < 18)) = true ∧
    (eval wit3).eo = eoZero ∧ (eval wit3).co = St.id.co ∧ maskOf (eval wit3).ep = idE := by
  have h := p3Low_true; unfold p3LowF p3LowW at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

def Inv3 (x : St) : Prop := cpSet.contains x.cp = true ∧ pairSet.contains (pkey x) = true ∧
  x.eo = eoZero ∧ x.co = St.id.co ∧ maskOf x.ep = idE

theorem inv3_apply {x : St} (hx : Inv3 x) {m : Nat} (hg : m ∈ g2Moves) : Inv3 (apply x m) := by
  have hm : m < 18 := by simp [g2Moves] at hg; omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  obtain ⟨e1, e2, e3⟩ := g2_keep [m] (by simp [hg]) x h3 h4 h5
  exact ⟨by rw [apply_cp]; exact cp_closed_step h1 m hm,
    pair_reach [m] (by simp [hm]) x h2, e1, e2, e3⟩

theorem p3_reach (w : List Nat) (hw : ∀ m ∈ w, m ∈ g2Moves) : ∀ x : St, Inv3 x →
    dOf (k3TableF ()) (key3 x) ≤ dOf (k3TableF ()) (key3 (applyList x w)) + w.length := by
  induction w with
  | nil => intro x _; simp [applyList]
  | cons h w ih =>
    intro x hx
    have hg : h ∈ g2Moves := hw h (by simp)
    have hp : pairSet.contains (idE, maskMSof x.ep) = true := by
      have e : pkey x = (idE, maskMSof x.ep) := by simp only [pkey, hx.2.2.2.2]
      rw [← e]; exact hx.2.1
    have hl := of_decide_eq_true ((List.all_eq_true.1 ((List.all_eq_true.1
      ((List.all_eq_true.1 p3_parts.1) (x.cp, ()) (mem_toList_of_contains hx.1))) _ (ms70_of hp))) h hg)
    have := ih (fun m hm => hw m (by simp [hm])) (apply x h) (inv3_apply hx hg)
    rw [applyList_cons']; rw [apply_key3] at this
    simp only [List.length_cons]; simp only [key3] at this ⊢; simp only at hl; omega

/-- **Thistlethwaite phase 3 needs 13 moves:** from the domino-reduced position `wit3`, no word in
<U,D,R2,L2,F2,B2> of fewer than 13 moves reaches the phase-4 subgroup coset. -/
theorem thistle_phase3_lower (w : List Nat) (hw : ∀ m ∈ w, m ∈ g2Moves)
    (h1 : hSet.contains (applyList (eval wit3) w).cp = true) (h2 : maskMSof (applyList (eval wit3) w).ep = idMS) :
    13 ≤ w.length := by
  have hs : ∀ m ∈ wit3, m < 18 := fun m hm => of_decide_eq_true ((List.all_eq_true.1 p3_parts.2.2.2.1) m hm)
  have hx : Inv3 (eval wit3) := ⟨cp_reach wit3 hs St.id cpId_true, pair_reach wit3 hs St.id pairId_true,
    p3_parts.2.2.2.2.1, p3_parts.2.2.2.2.2.1, p3_parts.2.2.2.2.2.2⟩
  have := p3_reach w hw _ hx
  have hz : dOf (k3TableF ()) (key3 (applyList (eval wit3) w)) = 0 := by
    have := (List.all_eq_true.1 p3_parts.2.1) _ (hList_of h1)
    simp only [beq_iff_eq] at this
    simp only [key3, h2]; exact this
  rw [hz, p3_parts.2.2.1] at this
  omega

#print axioms thistle_phase1_lower
#print axioms thistle_phase2_lower
#print axioms thistle_phase3_lower
