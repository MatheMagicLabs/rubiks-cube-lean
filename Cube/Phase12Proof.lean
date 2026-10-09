import Cube.Phase12Thm
open Std

theorem apply_eo (x : St) (m : Nat) : (apply x m).eo = eoAct x.eo m := rfl
theorem apply_co (x : St) (m : Nat) : (apply x m).co = coAct x.co m := rfl

theorem getElem!_map_cls (a : Array Nat) (j : Nat) : (a.map cls)[j]! = cls a[j]! := by
  by_cases h : j < a.size
  · have h' : j < (a.map cls).size := by simpa using h
    rw [getElem!_pos (a.map cls) j h', getElem!_pos a j h, Array.getElem_map]
  · have h' : ¬ j < (a.map cls).size := by simpa using h
    rw [getElem!_neg (a.map cls) j h', getElem!_neg a j h]
    rfl

theorem apply_mask (x : St) (m : Nat) : maskOf (apply x m).ep = maskAct (maskOf x.ep) m := by
  show ((List.range 12).toArray.map (fun i => x.ep[(moves[m]!).ep[i]!]!)).map cls =
    (List.range 12).toArray.map (fun i => (x.ep.map cls)[(moves[m]!).ep[i]!]!)
  rw [Array.map_map]
  congr 1
  funext i
  simp only [Function.comp, getElem!_map_cls]

def key2 (x : St) : K2 := (x.co, maskOf x.ep)
theorem apply_key2 (x : St) (m : Nat) : key2 (apply x m) = k2Act (key2 x) m := by
  simp only [key2, k2Act, apply_co, apply_mask]

theorem applyList_cons' (x : St) (h : Nat) (w : List Nat) : applyList x (h :: w) = applyList (apply x h) w := rfl

theorem applyList_eo (w : List Nat) : ∀ x : St, (applyList x w).eo = eoActList x.eo w := by
  induction w with
  | nil => intro x; rfl
  | cons h w ih => intro x; rw [applyList_cons', ih]; rfl

theorem applyList_key2 (w : List Nat) : ∀ x : St, key2 (applyList x w) = k2ActList (key2 x) w := by
  induction w with
  | nil => intro x; rfl
  | cons h w ih => intro x; rw [applyList_cons', ih, apply_key2]; rfl

-- ---------- phase 1 ----------
theorem eo_parts : (eoTable.toList.all (fun p => eoEntryOk p.1 p.2) = true) ∧ eoTable.contains eoZero = true := by
  have h := eoCheck_true; unfold eoCheck at h; rw [Bool.and_eq_true] at h; exact h

theorem eo_entry {e : Array Nat} {o : Option (List Nat)} (he : eoTable[e]? = some o) :
    ∃ w, o = some w ∧ w.length ≤ 7 ∧ (∀ m ∈ w, m < 18) ∧ eoActList e w = eoZero ∧
      ∀ m ∈ allMoves, eoTable.contains (eoAct e m) = true := by
  have hm : (e, o) ∈ eoTable.toList := (HashMap.mem_toList_iff_getElem?_eq_some).2 he
  have ok := (List.all_eq_true.1 eo_parts.1) (e, o) hm
  cases o with
  | none => exact absurd ok (by simp [eoEntryOk])
  | some w =>
    simp only [eoEntryOk, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ok
    refine ⟨w, rfl, h1, ?_, h3, List.all_eq_true.1 h4⟩
    intro m hm; exact of_decide_eq_true ((List.all_eq_true.1 h2) m hm)

theorem eo_some {e : Array Nat} (h : eoTable.contains e = true) : ∃ o, eoTable[e]? = some o := by
  rw [HashMap.contains_eq_isSome_getElem?] at h
  exact Option.isSome_iff_exists.1 h

theorem eo_reach (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∀ x : St, eoTable.contains x.eo = true → eoTable.contains (applyList x w).eo = true := by
  induction w with
  | nil => intro x hx; exact hx
  | cons h w ih =>
    intro x hx
    rw [applyList_cons']
    apply ih (fun m hm => hw m (by simp [hm]))
    obtain ⟨o, ho⟩ := eo_some hx
    obtain ⟨-, -, -, -, -, hcl⟩ := eo_entry ho
    rw [apply_eo]
    exact hcl h (by simpa [allMoves] using hw h (by simp))

/-- **Phase 1 (EO):** every position reachable from solved can have its edges oriented (F/B axis) in at most
7 face turns. -/
theorem phase1_eo (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∃ w', w'.length ≤ 7 ∧ (∀ m ∈ w', m < 18) ∧ (applyList (eval w) w').eo = eoZero := by
  have hc : eoTable.contains (eval w).eo = true := eo_reach w hw St.id eo_parts.2
  obtain ⟨o, ho⟩ := eo_some hc
  obtain ⟨w', rfl, h1, h2, h3, -⟩ := eo_entry ho
  exact ⟨w', h1, h2, by rw [applyList_eo]; exact h3⟩

#print axioms phase1_eo

-- ---------- phase 2 ----------
theorem k2_parts : (k2Table.toList.all (fun p => k2EntryOk p.1 p.2) = true) ∧ k2Table.contains k2Start = true := by
  have h := k2Check_true; unfold k2Check at h; rw [Bool.and_eq_true] at h; exact h

theorem k2_entry {k : K2} {o : Option (List Nat)} (hk : k2Table[k]? = some o) :
    ∃ w, o = some w ∧ w.length ≤ 10 ∧ (∀ m ∈ w, m ∈ g1Moves) ∧ k2ActList k w = k2Start ∧
      ∀ m ∈ allMoves, k2Table.contains (k2Act k m) = true := by
  have hm : (k, o) ∈ k2Table.toList := (HashMap.mem_toList_iff_getElem?_eq_some).2 hk
  have ok := (List.all_eq_true.1 k2_parts.1) (k, o) hm
  cases o with
  | none => exact absurd ok (by simp [k2EntryOk])
  | some w =>
    simp only [k2EntryOk, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ok
    refine ⟨w, rfl, h1, ?_, h3, List.all_eq_true.1 h4⟩
    intro m hm; exact List.contains_iff_mem.1 ((List.all_eq_true.1 h2) m hm)

theorem k2_some {k : K2} (h : k2Table.contains k = true) : ∃ o, k2Table[k]? = some o := by
  rw [HashMap.contains_eq_isSome_getElem?] at h
  exact Option.isSome_iff_exists.1 h

theorem k2_reach (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∀ x : St, k2Table.contains (key2 x) = true → k2Table.contains (key2 (applyList x w)) = true := by
  induction w with
  | nil => intro x hx; exact hx
  | cons h w ih =>
    intro x hx
    rw [applyList_cons']
    apply ih (fun m hm => hw m (by simp [hm]))
    obtain ⟨o, ho⟩ := k2_some hx
    obtain ⟨-, -, -, -, -, hcl⟩ := k2_entry ho
    rw [apply_key2]
    exact hcl h (by simpa [allMoves] using hw h (by simp))

theorem g1_keeps_eo (w : List Nat) (hw : ∀ m ∈ w, m ∈ g1Moves) : ∀ e, e = eoZero → eoActList e w = eoZero := by
  induction w with
  | nil => intro e he; exact he
  | cons h w ih =>
    intro e he
    have hk := (List.all_eq_true.1 (by have := g1KeepsEO_true; unfold g1KeepsEO at this; exact this)) h (hw h (by simp))
    exact ih (fun m hm => hw m (by simp [hm])) (eoAct e h) (by rw [he]; exact of_decide_eq_true hk)

theorem key2_start : key2 St.id = k2Start := rfl

/-- **Phase 2 (domino reduction):** from any reachable position with edges oriented, at most 10 moves of
⟨U, D, R, L, F2, B2⟩ orient all corners and bring the E-slice edges into the E slice, keeping EO. -/
theorem phase2_dr (w : List Nat) (hw : ∀ m ∈ w, m < 18) (heo : (eval w).eo = eoZero) :
    ∃ w', w'.length ≤ 10 ∧ (∀ m ∈ w', m ∈ g1Moves) ∧
      (applyList (eval w) w').eo = eoZero ∧ key2 (applyList (eval w) w') = key2 St.id := by
  have hc : k2Table.contains (key2 (eval w)) = true := k2_reach w hw St.id (by rw [key2_start]; exact k2_parts.2)
  obtain ⟨o, ho⟩ := k2_some hc
  obtain ⟨w', rfl, h1, h2, h3, -⟩ := k2_entry ho
  refine ⟨w', h1, h2, ?_, ?_⟩
  · rw [applyList_eo]; exact g1_keeps_eo w' h2 _ heo
  · rw [applyList_key2, h3, key2_start]

#print axioms phase2_dr
