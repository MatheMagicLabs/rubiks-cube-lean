import Cube.Phase34Proof
import Cube.Phase4Thm
import Cube.ParityLaw
open Std

/-! Composition of the four Thistlethwaite phases (7 + 10 + 13 + 15 = 45 moves). -/

theorem applyList_append (x : St) (u v : List Nat) : applyList x (u ++ v) = applyList (applyList x u) v := by
  unfold applyList; exact List.foldl_append
theorem eval_append (u v : List Nat) : eval (u ++ v) = applyList (eval u) v := applyList_append _ _ _

theorem g1_lt {m : Nat} (h : m ∈ g1Moves) : m < 18 := by simp [g1Moves] at h; omega
theorem g2_lt {m : Nat} (h : m ∈ g2Moves) : m < 18 := by simp [g2Moves] at h; omega
theorem half_lt {m : Nat} (h : m ∈ half) : m < 18 := by simp [half] at h; omega

theorem all_append {p : Nat → Prop} {u v : List Nat} (hu : ∀ m ∈ u, p m) (hv : ∀ m ∈ v, p m) : ∀ m ∈ u ++ v, p m := by
  intro m hm; rcases List.mem_append.1 hm with h | h
  · exact hu m h
  · exact hv m h

/-- **Phase 3:** from a domino-reduced position, at most 13 moves of <U,D,R2,L2,F2,B2> bring the corners into the
half-turn group's corner permutations and the M-slice edges into the M slice. -/
theorem phase3_htr (u : List Nat) (hu : ∀ m ∈ u, m < 18) (heo : (eval u).eo = eoZero)
    (hk : key2 (eval u) = key2 St.id) :
    ∃ w, w.length ≤ 13 ∧ (∀ m ∈ w, m ∈ g2Moves) ∧ (applyList (eval u) w).eo = eoZero ∧
      (applyList (eval u) w).co = St.id.co ∧ maskOf (applyList (eval u) w).ep = idE ∧
      hSet.contains (applyList (eval u) w).cp = true ∧ maskMSof (applyList (eval u) w).ep = idMS := by
  have hco : (eval u).co = St.id.co := congrArg Prod.fst hk
  have hmk : maskOf (eval u).ep = idE := congrArg Prod.snd hk
  have hcp : cpSet.contains (eval u).cp = true := cp_reach u hu St.id cpId_true
  have hp : pairSet.contains (pkey (eval u)) = true := pair_reach u hu St.id pairId_true
  have hp' : pairSet.contains (idE, maskMSof (eval u).ep) = true := by
    have e : pkey (eval u) = (idE, maskMSof (eval u).ep) := by simp only [pkey, hmk]
    rw [e] at hp; exact hp
  obtain ⟨w, hl, hg, ht⟩ := k3_entry (mem_toList_of_contains hcp) (ms70_of hp')
  obtain ⟨e1, e2, e3⟩ := g2_keep w hg (eval u) heo hco hmk
  have ht' : k3Target (key3 (applyList (eval u) w)) = true := by rw [applyList_key3]; exact ht
  simp only [k3Target, key3, Bool.and_eq_true, beq_iff_eq] at ht'
  exact ⟨w, hl, hg, e1, e2, e3, ht'.1, ht'.2⟩

theorem F2_of : ∀ (l : List Nat) (As : List (List Nat)), l.length = As.length →
    (∀ i (h1 : i < l.length) (h2 : i < As.length), l[i] ∈ As[i]) → F2 l As
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, A :: As, h, hi => by
    show a ∈ A ∧ F2 l As
    refine ⟨by simpa using hi 0 (by simp) (by simp), F2_of l As (by simpa using h) ?_⟩
    intro i h1 h2
    simpa using hi (i + 1) (by simpa using h1) (by simpa using h2)

theorem slice_mem (x : St) (hg : Good x) (hE : maskOf x.ep = idE) (hM : maskMSof x.ep = idMS) :
    ∀ i (h1 : i < x.ep.toList.length) (h2 : i < sliceSets.length), x.ep.toList[i] ∈ sliceSets[i] := by
  intro i h1 h2
  have hi12 : i < 12 := by simpa [sliceSets] using h2
  have hsz : x.ep.size = 12 := hg.2.1
  have hmem : x.ep.toList[i] ∈ List.range 12 := hg.2.2.2.1.mem_iff.1 (List.getElem_mem h1)
  have he : x.ep.toList[i] < 12 := List.mem_range.1 hmem
  have hx : x.ep[i]! = x.ep.toList[i] := by
    rw [getElem!_pos x.ep i (by omega), Array.getElem_toList]
  have hc1 : cls x.ep.toList[i] = idE[i]! := by
    rw [← hx, ← hE]; exact (getElem!_map_cls x.ep i).symm
  have hc2 : clsM x.ep.toList[i] = idMS[i]! := by
    rw [← hx, ← hM]; exact (getElem!_map_clsM x.ep i).symm
  have hs := sliceOk_true; unfold sliceOk at hs
  have h3 := List.all_eq_true.1 ((List.all_eq_true.1 hs) i (List.mem_range.2 hi12)) _ (List.mem_range.2 he)
  rw [← hc1, ← hc2] at h3
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at h3
  rw [getElem!_pos sliceSets i h2] at h3
  exact List.contains_iff_mem.1 h3

/-- **Phase 4:** a position in the half-turn group (corners in H, edges in their slices, all oriented) is solved by
at most 15 half turns. -/
theorem phase4_sq (u : List Nat) (hu : ∀ m ∈ u, m < 18) (heo : (eval u).eo = eoZero) (hco : (eval u).co = St.id.co)
    (hE : maskOf (eval u).ep = idE) (hH : hSet.contains (eval u).cp = true) (hM : maskMSof (eval u).ep = idMS) :
    ∃ w, w.length ≤ 15 ∧ (∀ m ∈ w, m ∈ half) ∧ applyList (eval u) w = St.id := by
  have hg : Good (eval u) := parity_law u hu
  have hcpL : (eval u).cp ∈ hList := hList_of hH
  have hev : inv (eval u).cp.toList % 2 = 0 := by
    have h := hEven_true; unfold hEven at h
    exact of_decide_eq_true ((List.all_eq_true.1 h) _ hcpL)
  have hep : inv (eval u).ep.toList % 2 = 0 := by have := hg.2.2.2.2; omega
  have hF : F2 (eval u).ep.toList sliceSets :=
    F2_of _ _ (by simp [sliceSets, hg.2.1]) (slice_mem (eval u) hg hE hM)
  have hnd : (eval u).ep.toList.Nodup := hg.2.2.2.1.nodup_iff.2 List.nodup_range
  have hfc := fiberCheck_true; unfold fiberCheckF fiberCheckW at hfc
  have hP := allSel_spec sliceSets [] _ hfc (eval u).ep.toList hF (by simpa using hnd)
  simp only [List.nil_append] at hP
  unfold fiberPW at hP
  have hodd : (inv (eval u).ep.toList % 2 != 0) = false := by simp [hep]
  rw [hodd, Bool.false_or] at hP
  have hs : solOk ⟨(eval u).cp, zeros8, (eval u).ep.toList.toArray, zeros12⟩
      (sqSolveF ())[(⟨(eval u).cp, zeros8, (eval u).ep.toList.toArray, zeros12⟩ : St)]? = true :=
    (List.all_eq_true.1 hP) _ hcpL
  have hxe : (⟨(eval u).cp, zeros8, (eval u).ep.toList.toArray, zeros12⟩ : St) = eval u := by
    have e1 : zeros8 = (eval u).co := hco.symm
    have e2 : zeros12 = (eval u).eo := heo.symm
    rw [e1, e2, Array.toArray_toList]
  rw [hxe] at hs
  unfold solOk at hs
  revert hs
  generalize (sqSolveF ())[eval u]? = q
  intro hs
  cases q with
  | none => exact absurd hs (by simp)
  | some o =>
    cases o with
    | none => exact absurd hs (by simp)
    | some w =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      refine ⟨w, hs.1.1, ?_, hs.2⟩
      intro m hm; exact List.contains_iff_mem.1 ((List.all_eq_true.1 hs.1.2) m hm)

/-- **Thistlethwaite's 45-move bound**, formally: every position reachable with face turns (half-turn metric) is
solved by a word of at most 45 face turns. -/
theorem thistlethwaite_45 (w : List Nat) (hw : ∀ m ∈ w, m < 18) :
    ∃ W : List Nat, W.length ≤ 45 ∧ (∀ m ∈ W, m < 18) ∧ applyList (eval w) W = St.id := by
  obtain ⟨w1, l1, m1, e1⟩ := phase1_eo w hw
  rw [← eval_append] at e1
  have hu1 := all_append hw m1
  obtain ⟨w2, l2, m2, e2, k2⟩ := phase2_dr (w ++ w1) hu1 e1
  have m2' : ∀ m ∈ w2, m < 18 := fun m hm => g1_lt (m2 m hm)
  rw [← eval_append] at e2 k2
  have hu2 := all_append hu1 m2'
  obtain ⟨w3, l3, m3, f1, f2, f3, f4, f5⟩ := phase3_htr (w ++ w1 ++ w2) hu2 e2 k2
  have m3' : ∀ m ∈ w3, m < 18 := fun m hm => g2_lt (m3 m hm)
  rw [← eval_append] at f1 f2 f3 f4 f5
  have hu3 := all_append hu2 m3'
  obtain ⟨w4, l4, m4, g⟩ := phase4_sq (w ++ w1 ++ w2 ++ w3) hu3 f1 f2 f3 f4 f5
  have m4' : ∀ m ∈ w4, m < 18 := fun m hm => half_lt (m4 m hm)
  refine ⟨w1 ++ w2 ++ w3 ++ w4, ?_, all_append (all_append (all_append m1 m2') m3') m4', ?_⟩
  · simp only [List.length_append]; omega
  · rw [applyList_append, applyList_append, applyList_append, ← eval_append, ← eval_append, ← eval_append]
    exact g

#print axioms thistlethwaite_45
