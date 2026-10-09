import CubeP.Phase34Thm
import CubeP.Phase12Proof
open Std

theorem getElem!_map_clsM (a : Array Nat) (j : Nat) : (a.map clsM)[j]! = clsM a[j]! := by
  by_cases h : j < a.size
  · have h' : j < (a.map clsM).size := by simpa using h
    rw [getElem!_pos (a.map clsM) j h', getElem!_pos a j h, Array.getElem_map]
  · have h' : ¬ j < (a.map clsM).size := by simpa using h
    rw [getElem!_neg (a.map clsM) j h', getElem!_neg a j h]
    rfl

theorem apply_maskMS (x : St) (m : Nat) : maskMSof (apply x m).ep = maskAct (maskMSof x.ep) m := by
  show ((List.range 12).toArray.map (fun i => x.ep[(moves[m]!).ep[i]!]!)).map clsM =
    (List.range 12).toArray.map (fun i => (x.ep.map clsM)[(moves[m]!).ep[i]!]!)
  rw [Array.map_map]
  congr 1
  funext i
  simp only [Function.comp, getElem!_map_clsM]

theorem apply_cp (x : St) (m : Nat) : (apply x m).cp = cpAct x.cp m := rfl

-- generic: membership in a closure table from `contains`
theorem mem_toList_of_contains {K : Type} [BEq K] [Hashable K] [LawfulBEq K] {t : HashMap K Unit} {k : K}
    (h : t.contains k = true) : (k, ()) ∈ t.toList := by
  rw [HashMap.contains_eq_isSome_getElem?] at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  cases v
  exact (HashMap.mem_toList_iff_getElem?_eq_some).2 hv

theorem cp_closed_step {c : Array Nat} (h : cpSet.contains c = true) (m : Nat) (hm : m < 18) :
    cpSet.contains (cpAct c m) = true := by
  have hc := cpClosed_true; unfold cpClosed at hc
  have := (List.all_eq_true.1 hc) (c, ()) (mem_toList_of_contains h)
  exact (List.all_eq_true.1 this) m (by simpa [allMoves] using hm)

theorem cp_reach (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∀ x : St, cpSet.contains x.cp = true → cpSet.contains (applyList x w).cp = true := by
  induction w with
  | nil => intro x hx; exact hx
  | cons h w ih =>
    intro x hx
    rw [applyList_cons']
    apply ih (fun m hm => hw m (by simp [hm]))
    rw [apply_cp]; exact cp_closed_step hx h (hw h (by simp))

def pkey (x : St) : PK := (maskOf x.ep, maskMSof x.ep)
theorem apply_pkey (x : St) (m : Nat) : pkey (apply x m) = pkAct (pkey x) m := by
  simp only [pkey, pkAct, apply_mask, apply_maskMS]

theorem pair_reach (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∀ x : St, pairSet.contains (pkey x) = true → pairSet.contains (pkey (applyList x w)) = true := by
  induction w with
  | nil => intro x hx; exact hx
  | cons h w ih =>
    intro x hx
    rw [applyList_cons']
    apply ih (fun m hm => hw m (by simp [hm]))
    rw [apply_pkey]
    have hc := pairClosed_true; unfold pairClosed at hc
    have := (List.all_eq_true.1 hc) (pkey x, ()) (mem_toList_of_contains hx)
    exact (List.all_eq_true.1 this) h (by simpa [allMoves] using hw h (by simp))

theorem ms70_of {k : Array Nat} (h : pairSet.contains (idE, k) = true) : k ∈ ms70 := by
  unfold ms70
  rw [List.mem_map]
  exact ⟨((idE, k), ()), List.mem_filter.2 ⟨mem_toList_of_contains h, by simp⟩, rfl⟩

theorem hList_of {c : Array Nat} (h : hSet.contains c = true) : c ∈ hList := by
  unfold hList
  rw [List.mem_map]
  exact ⟨(c, ()), mem_toList_of_contains h, rfl⟩

def key3 (x : St) : K3 := (x.cp, maskMSof x.ep)
theorem apply_key3 (x : St) (m : Nat) : key3 (apply x m) = k3Act (key3 x) m := by
  simp only [key3, k3Act, apply_cp, apply_maskMS]
theorem applyList_key3 (w : List Nat) : ∀ x : St, key3 (applyList x w) = k3ActList (key3 x) w := by
  induction w with
  | nil => intro x; rfl
  | cons h w ih => intro x; rw [applyList_cons', ih, apply_key3]; rfl

theorem g2_props (m : Nat) (hm : m ∈ g2Moves) :
    m ∈ g1Moves ∧ coAct St.id.co m = St.id.co ∧ maskAct idE m = idE := by
  have h := g2Keep_true; unfold g2Keep at h
  have := (List.all_eq_true.1 h) m hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨List.contains_iff_mem.1 this.1.1, this.1.2, this.2⟩

theorem g2_keep (w : List Nat) (hw : ∀ m ∈ w, m ∈ g2Moves) : ∀ x : St,
    x.eo = eoZero → x.co = St.id.co → maskOf x.ep = idE →
    (applyList x w).eo = eoZero ∧ (applyList x w).co = St.id.co ∧ maskOf (applyList x w).ep = idE := by
  induction w with
  | nil => intro x h1 h2 h3; exact ⟨h1, h2, h3⟩
  | cons h w ih =>
    intro x h1 h2 h3
    obtain ⟨hg1, hco, hmk⟩ := g2_props h (hw h (by simp))
    rw [applyList_cons']
    apply ih (fun m hm => hw m (by simp [hm]))
    · rw [apply_eo, h1]
      have hk := (List.all_eq_true.1 (by have := g1KeepsEO_true; unfold g1KeepsEO at this; exact this)) h hg1
      exact of_decide_eq_true hk
    · rw [apply_co, h2]; exact hco
    · rw [apply_mask, h3]; exact hmk

theorem k3_entry {cp k : Array Nat} (hcp : (cp, ()) ∈ cpSet.toList) (hk : k ∈ ms70) :
    ∃ w, w.length ≤ 13 ∧ (∀ m ∈ w, m ∈ g2Moves) ∧ k3Target (k3ActList (cp, k) w) = true := by
  have h := k3Check_true; unfold k3CheckF k3CheckW at h
  have h1 := (List.all_eq_true.1 h) (cp, ()) hcp
  have h2 := (List.all_eq_true.1 h1) k hk
  unfold k3OkW at h2
  revert h2
  generalize (k3TableF ())[(cp, k)]? = q
  intro h2
  cases q with
  | none => exact absurd h2 (by simp)
  | some o =>
    cases o with
    | none => exact absurd h2 (by simp)
    | some w =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      refine ⟨w, h2.1.1, ?_, h2.2⟩
      intro m hm; exact List.contains_iff_mem.1 ((List.all_eq_true.1 h2.1.2) m hm)
