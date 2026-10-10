import CubeP.ScNorm
import CubeP.SfProof
import CubeS.ScThm
open Std

/-! **On the supercube, the superflip with all centres at home needs 22 face turns.** No word of at most 21 face
turns turns the solved cube into the superflip while turning every face centre by a multiple of 360°. -/

theorem leafS_zero (d2 : ByteArray) (tgt : Sig) (need : Nat) (p : P) (lf : Nat) (first : Bool) (s : Sig) :
    leafS d2 tgt 0 need p lf first s = ((!(need == 0 && p == idP && decide (s = tgt))) && true) := rfl

theorem leafS_succ (d2 : ByteArray) (tgt : Sig) (r need : Nat) (p : P) (lf : Nat) (first : Bool) (s : Sig) :
    leafS d2 tgt (r + 1) need p lf first s =
      ((!(need == 0 && p == idP && decide (s = tgt))) &&
       allLt (fun t =>
         (g2A[t]! / 3 == lf) || (!first && (g2A[t]! / 3) % 3 == lf % 3 && g2A[t]! / 3 < lf) ||
         decide (r + 1 < need) ||
         (decide (r < (d2.get! (cellOf (pAct p g2A[t]!))).toNat) ||
           leafS d2 tgt r (need - 1) (pAct p g2A[t]!) (g2A[t]! / 3) false (sigStep s g2A[t]!))) 10) := rfl

theorem scSearch_zero (d1 d2 : ByteArray) (B : Nat) (tgt : Sig) (r0 r1 r2 : Nat) (p : P) (g lastf : Nat)
    (rs : RunSt) (lnh : Bool) (s : Sig) :
    scSearch d1 d2 B tgt 0 r0 r1 r2 p g lastf rs lnh s =
      ((!(lnh && (d1.get! r0).toNat == 0) || leafS d2 tgt (B - g) rs.mx p lastf true s) && true) := rfl

theorem scSearch_succ (d1 d2 : ByteArray) (B : Nat) (tgt : Sig) (f r0 r1 r2 : Nat) (p : P) (g lastf : Nat)
    (rs : RunSt) (lnh : Bool) (s : Sig) :
    scSearch d1 d2 B tgt (f + 1) r0 r1 r2 p g lastf rs lnh s =
      ((!(lnh && (d1.get! r0).toNat == 0) || leafS d2 tgt (B - g) rs.mx p lastf true s) &&
       allLt (fun m =>
         !(okNext lastf m) || (g == 0 && !(m == 3 || m == 5)) ||
         (decide (B < g + 1 + (d1.get! (next r0 m)).toNat + (runStep rs m).mx) ||
          decide (B < g + 1 + (d1.get! (next r1 (muS m))).toNat) ||
          decide (B < g + 1 + (d1.get! (next r2 (muS (muS m)))).toNat) ||
          scSearch d1 d2 B tgt f (next r0 m) (next r1 (muS m)) (next r2 (muS (muS m))) (pAct p m) (g + 1) (m / 3)
            (runStep rs m) (!isHUD m) (sigStep s m))) 18) := by
  rw [scSearch]; simp only [traceIf_eq]

/-- order rule inside `s2`: the first move only avoids the face `lf`; later moves follow the canonical rule -/
def OrdH : Nat → Bool → List Nat → Prop
  | _, _, [] => True
  | lf, first, m :: t => m / 3 ≠ lf ∧ (first = true ∨ ¬((m / 3) % 3 = lf % 3 ∧ m / 3 < lf)) ∧ OrdH (m / 3) false t

theorem g2A_of_mem {m : Nat} (h : m ∈ g2Moves) : ∃ t, t < 10 ∧ g2A[t]! = m := by
  simp only [g2Moves, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩
  · exact ⟨8, by decide, rfl⟩
  · exact ⟨9, by decide, rfl⟩

theorem pActList_cons' (p : P) (m : Nat) (t : List Nat) : pActList p (m :: t) = pActList (pAct p m) t := rfl

/-- **Specification of the leaf enumeration.** -/
theorem leaf_spec (tgt : Sig) : ∀ (rem need : Nat) (pp : P) (lf : Nat) (first : Bool) (s : Sig), Dom pp →
    leafS (dist2F ()) tgt rem need pp lf first s = true →
    ∀ s2 : List Nat, (∀ m ∈ s2, m ∈ g2Moves) → s2.length ≤ rem → need ≤ s2.length → OrdH lf first s2 →
      pActList pp s2 = idP → s2.foldl sigStep s = tgt → False := by
  intro rem
  induction rem with
  | zero =>
    intro need pp lf first s _ hL s2 hs2 hlen hneed _ hid hsig
    have h0 : s2 = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    rw [leafS_zero] at hL
    have hn : need = 0 := by simp at hneed; omega
    have hp : pp = idP := hid
    have hs : s = tgt := hsig
    subst hn hp hs
    simp at hL
  | succ r ih =>
    intro need pp lf first s hdom hL s2 hs2 hlen hneed hord hid hsig
    rw [leafS_succ, Bool.and_eq_true] at hL
    obtain ⟨hA, hB⟩ := hL
    cases s2 with
    | nil =>
      have hn : need = 0 := by simp at hneed; omega
      have hp : pp = idP := hid
      have hs : s = tgt := hsig
      subst hn hp hs
      simp at hA
    | cons m t =>
      have hm : m ∈ g2Moves := hs2 m (by simp)
      obtain ⟨i, hi, hgi⟩ := g2A_of_mem hm
      have hc := allLt_spec _ 10 hB i hi
      simp only [hgi] at hc
      obtain ⟨hf1, hf2, hord'⟩ := hord
      have ht2 : ∀ k ∈ t, k ∈ g2Moves := fun k hk => hs2 k (by simp [hk])
      have htl : t.length ≤ r := by simp at hlen; omega
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc
      rcases hc with ((h1 | h2) | h3) | h4 | h5
      · exact hf1 h1
      · rcases hf2 with hfst | hnd
        · rw [hfst] at h2; simp at h2
        · exact hnd ⟨h2.1.2, h2.2⟩
      · simp at hneed; omega
      · have h4' := h4
        have hdom' : Dom (pAct pp m) := dom_act hdom hm
        have hl := lip2_reach t ht2 _ hdom'
        have e : pActList (pAct pp m) t = idP := hid
        rw [e] at hl
        have e2 : cellOf idP = idCell := rfl
        rw [e2, low2_parts.2.1] at hl
        omega
      · exact ih (need - 1) (pAct pp m) (m / 3) false (sigStep s m) (dom_act hdom hm) h5 t ht2 htl
          (by simp at hneed; omega) hord' hid hsig

theorem sigOf_append (u v : List Nat) : sigOf (u ++ v) = v.foldl sigStep (sigOf u) := by
  unfold sigOf; rw [List.foldl_append]

theorem canon_tail {prev : Nat} {t : List Nat} (h : Canon (prev :: t)) : Canon t := by
  intro u v a b e; exact h (prev :: u) v a b (by rw [e]; simp)

theorem ordH_false : ∀ (t : List Nat) (prev : Nat) (u : List Nat), NoAdj (u ++ prev :: t) → Canon (prev :: t) →
    OrdH (prev / 3) false t := by
  intro t
  induction t with
  | nil => intro _ _ _ _; trivial
  | cons m2 t2 ih =>
    intro prev u hadj hcan
    refine ⟨fun e => hadj u t2 prev m2 (by simp) e.symm, Or.inr (fun hd => hcan [] t2 prev m2 (by simp) hd), ?_⟩
    exact ih m2 (u ++ [prev]) (by simpa using hadj) (canon_tail hcan)

/-- order facts of the normal form give the order rule for `s2` -/
theorem ordH_of {s2 : List Nat} (i : List Nat) (l : Nat) (hadj : NoAdj (i ++ [l] ++ s2)) (hcan : Canon s2) :
    OrdH (l / 3) true s2 := by
  cases s2 with
  | nil => trivial
  | cons m t =>
    refine ⟨fun e => hadj i t l m (by simp) e.symm, Or.inl rfl, ?_⟩
    exact ordH_false t m (i ++ [l]) (by simpa using hadj) hcan

theorem pActList_app (p : P) (u v : List Nat) : pActList p (u ++ v) = pActList (pActList p u) v := by
  unfold pActList; rw [List.foldl_append]

theorem okNext_false {lf m : Nat} (h : okNext lf m = false) :
    m / 3 = lf ∨ (lf < 6 ∧ (m / 3) % 3 = lf % 3 ∧ m / 3 < lf) := by
  unfold okNext at h
  by_cases h1 : m / 3 = lf
  · exact Or.inl h1
  · right
    have e : (m / 3 != lf) = true := by simp [h1]
    rw [e, Bool.true_and] at h
    cases hb : (decide (lf < 6) && (m / 3 % 3 == lf % 3) && decide (m / 3 < lf)) with
    | false => rw [hb] at h; simp at h
    | true =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      exact ⟨hb.1.1, hb.1.2, hb.2⟩

/-- **Specification of the search.** -/
theorem sc_spec : ∀ (f : Nat) (p : List Nat) (r0 r1 r2 : Nat) (pp : P) (lastf : Nat) (rs : RunSt) (lnh : Bool)
    (s : Sig),
    f + p.length = 21 → (∀ m ∈ p, m < 18) →
    r0 = rank (applyList sfSt p) → r1 = rank (applyList sfSt (p.map muS)) →
    r2 = rank (applyList sfSt ((p.map muS).map muS)) → pp = pActList idP p →
    (p = [] → lastf = 6) → (∀ i l, p = i ++ [l] → lastf = l / 3) → rs = runOf p →
    (lnh = true ↔ ∃ i l, p = i ++ [l] ∧ isHUD l = false) → s = sigOf p →
    scSearch (distF ()) (dist2F ()) 21 sig0 f r0 r1 r2 pp p.length lastf rs lnh s = true →
    ∀ q : List Nat, (∀ m ∈ q, m < 18) → NoAdj (p ++ q) → Canon (p ++ q) →
      (p = [] → ∃ x t, q = x :: t ∧ (x = 3 ∨ x = 5)) →
      (∃ i l, p ++ q = i ++ [l] ∧ isHUD l = false) →
      ∀ s2 : List Nat, (∀ m ∈ s2, m ∈ g2Moves) → applyList sfSt ((p ++ q) ++ s2) = St.id →
        (runOf (p ++ q)).mx ≤ s2.length → (∀ i l, p ++ q = i ++ [l] → OrdH (l / 3) true s2) →
        sigOf ((p ++ q) ++ s2) = sig0 → 21 < p.length + q.length + s2.length := by
  intro f
  induction f with
  | zero =>
    intro p r0 r1 r2 pp lastf rs lnh s hf hp hr0 hr1 hr2 hpp hl0 hl1 hrs hlnh hsg hs q hq hadj hcan hhead hlast s2
      hs2 hsol hmx hord hsig
    cases q with
    | cons m q' => simp; omega
    | nil =>
      rw [scSearch_zero, Bool.and_true] at hs
      simp only [List.append_nil] at hlast hsol hmx hord hsig
      rcases Nat.lt_or_ge 21 (p.length + s2.length) with hgt | hle
      · simp; omega
      · exfalso
        obtain ⟨hrk, -⟩ := leaf_bound hp hs2 hsol
        obtain ⟨i, l, hil, hl⟩ := hlast
        have hlt : lnh = true := hlnh.2 ⟨i, l, hil, hl⟩
        rw [hr0, hrk, low_parts.2.1, hlt] at hs
        simp only [Bool.true_and, beq_self_eq_true, Bool.not_true, Bool.false_or] at hs
        have hdom : Dom pp := by
          rw [hpp]
          have Vx := valid_applyList p hp sfSt sfValid
          have hsol' := hsol; rw [applyList_append] at hsol'
          have := (hform_of_solved Vx hs2 hsol').2
          rw [(applyList_pact p sfSt)] at this
          exact this
        refine leaf_spec sig0 (21 - p.length) rs.mx pp lastf true s hdom hs s2 hs2 (by omega) (by rw [hrs]; exact hmx)
          (by rw [hl1 i l hil]; exact hord i l hil) ?_ ?_
        · have e1 : pActList idP (p ++ s2) = ((applyList sfSt (p ++ s2)).cp, (applyList sfSt (p ++ s2)).ep) :=
            (applyList_pact (p ++ s2) sfSt).symm
          rw [hsol] at e1
          rw [hpp, ← pActList_app]; exact e1
        · rw [hsg, ← sigOf_append]; exact hsig
  | succ f ih =>
    intro p r0 r1 r2 pp lastf rs lnh s hf hp hr0 hr1 hr2 hpp hl0 hl1 hrs hlnh hsg hs q hq hadj hcan hhead hlast s2
      hs2 hsol hmx hord hsig
    rw [scSearch_succ, Bool.and_eq_true] at hs
    obtain ⟨hA, hB⟩ := hs
    cases q with
    | nil =>
      simp only [List.append_nil] at hlast hsol hmx hord hsig
      rcases Nat.lt_or_ge 21 (p.length + s2.length) with hgt | hle
      · simp; omega
      · exfalso
        obtain ⟨hrk, -⟩ := leaf_bound hp hs2 hsol
        obtain ⟨i, l, hil, hl⟩ := hlast
        have hlt : lnh = true := hlnh.2 ⟨i, l, hil, hl⟩
        rw [hr0, hrk, low_parts.2.1, hlt] at hA
        simp only [Bool.true_and, beq_self_eq_true, Bool.not_true, Bool.false_or] at hA
        have hdom : Dom pp := by
          rw [hpp]
          have Vx := valid_applyList p hp sfSt sfValid
          have hsol' := hsol; rw [applyList_append] at hsol'
          have := (hform_of_solved Vx hs2 hsol').2
          rw [(applyList_pact p sfSt)] at this
          exact this
        refine leaf_spec sig0 (21 - p.length) rs.mx pp lastf true s hdom hA s2 hs2 (by omega) (by rw [hrs]; exact hmx)
          (by rw [hl1 i l hil]; exact hord i l hil) ?_ ?_
        · have e1 : pActList idP (p ++ s2) = ((applyList sfSt (p ++ s2)).cp, (applyList sfSt (p ++ s2)).ep) :=
            (applyList_pact (p ++ s2) sfSt).symm
          rw [hsol] at e1
          rw [hpp, ← pActList_app]; exact e1
        · rw [hsg, ← sigOf_append]; exact hsig
    | cons m q' =>
      have hm18 : m < 18 := hq m (by simp)
      have hq' : ∀ k ∈ q', k < 18 := fun k hk => hq k (by simp [hk])
      have hpm : ∀ k ∈ p ++ [m], k < 18 := all_append hp (by simp [hm18])
      have hall : ∀ k ∈ p ++ m :: q', k < 18 := all_append hp hq
      have hs2' : ∀ k ∈ s2, k < 18 := fun k hk => g2_lt (hs2 k hk)
      have hc := allLt_spec _ 18 hB m hm18
      simp only at hc
      rw [Bool.or_eq_true, Bool.or_eq_true] at hc
      rcases hc with (horder | hfirst) | hrest
      · -- the order rule of the search excludes this move
        exfalso
        have hon : okNext lastf m = false := by simpa using horder
        have horder' := okNext_false hon
        cases hrev : p.reverse with
        | nil =>
          have hp0 : p = [] := List.reverse_eq_nil_iff.1 hrev
          have := hl0 hp0
          rcases horder' with h | h
          · omega
          · omega
        | cons l t =>
          have hil : p = t.reverse ++ [l] := by rw [← List.reverse_reverse p, hrev]; simp
          have hlf := hl1 _ _ hil
          rcases horder' with h | ⟨-, hax, hlt⟩
          · exact hadj t.reverse q' l m (by rw [hil]; simp) (by omega)
          · exact hcan t.reverse q' l m (by rw [hil]; simp) ⟨by omega, by omega⟩
      · -- the first move must be R or R'
        exfalso
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne,
          ne_eq] at hfirst
        have hp0 : p = [] := List.eq_nil_of_length_eq_zero hfirst.1
        obtain ⟨x, t, hxt, hx⟩ := hhead hp0
        simp only [List.cons.injEq] at hxt
        rw [← hxt.1] at hx
        omega
      · rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at hrest
        have hsolL : applyList sfSt (p ++ m :: q' ++ s2) = St.id := hsol
        have hleaf := (leaf_bound hall hs2 hsolL).1
        have hmxle : (runOf (p ++ [m])).mx ≤ s2.length := by
          have := runOf_mx_mono (p ++ [m]) q'
          rw [List.append_assoc] at this
          simp only [List.singleton_append] at this
          omega
        have hrank0 : next r0 m = rank (applyList sfSt (p ++ [m])) := by
          rw [hr0, ← rank_apply _ (inC_sf p hp) m hm18, applyList_append]; rfl
        have hrank1 : next r1 (muS m) = rank (applyList sfSt ((p ++ [m]).map muS)) := by
          rw [hr1, ← rank_apply _ (inC_sf _ (map_lt (μ := muS) (fun k hk => muS_lt hk) hp)) _ (muS_lt hm18), List.map_append,
            applyList_append]; rfl
        have hrank2 : next r2 (muS (muS m)) = rank (applyList sfSt (((p ++ [m]).map muS).map muS)) := by
          rw [hr2, ← rank_apply _ (inC_sf _ (map_lt (μ := muS) (fun k hk => muS_lt hk) (map_lt (μ := muS) (fun k hk => muS_lt hk) hp)))
            _ (muS_lt (muS_lt hm18)), List.map_append, List.map_append, applyList_append]; rfl
        have hrs' : runStep rs m = runOf (p ++ [m]) := by rw [hrs, runOf_snoc]
        rcases hrest with ((h0 | h1) | h2) | hrec
        · have h0' := of_decide_eq_true h0
          rw [hrank0, hrs'] at h0'
          have hlip := lip_reach q' hq' _ (inC_sf _ hpm)
          rw [← applyList_append, List.append_assoc, List.singleton_append, hleaf, low_parts.2.1] at hlip
          simp only [List.length_cons]
          omega
        · have h1' := of_decide_eq_true h1
          rw [hrank1] at h1'
          have hs := sol_mapS (all_append hall hs2') hsolL
          have e : (p ++ m :: q' ++ s2).map muS = (p ++ [m]).map muS ++ (q' ++ s2).map muS := by simp
          rw [e] at hs
          have := d1_bound (map_lt (μ := muS) (fun k hk => muS_lt hk) hpm)
            (map_lt (μ := muS) (fun k hk => muS_lt hk) (all_append hq' hs2')) hs
          simp only [List.length_map, List.length_append] at this
          simp only [List.length_cons]
          omega
        · have h2' := of_decide_eq_true h2
          rw [hrank2] at h2'
          have hs := sol_mapS (map_lt (μ := muS) (fun k hk => muS_lt hk) (all_append hall hs2'))
            (sol_mapS (all_append hall hs2') hsolL)
          have e : ((p ++ m :: q' ++ s2).map muS).map muS =
              ((p ++ [m]).map muS).map muS ++ ((q' ++ s2).map muS).map muS := by simp
          rw [e] at hs
          have := d1_bound (map_lt (μ := muS) (fun k hk => muS_lt hk) (map_lt (μ := muS) (fun k hk => muS_lt hk) hpm))
            (map_lt (μ := muS) (fun k hk => muS_lt hk) (map_lt (μ := muS) (fun k hk => muS_lt hk) (all_append hq' hs2'))) hs
          simp only [List.length_map, List.length_append] at this
          simp only [List.length_cons]
          omega
        · have hlen : (p ++ [m]).length = p.length + 1 := by simp
          have := ih (p ++ [m]) (next r0 m) (next r1 (muS m)) (next r2 (muS (muS m))) (pAct pp m) (m / 3) (runStep rs m)
            (!isHUD m) (sigStep s m) (by rw [hlen]; omega) hpm hrank0 hrank1 hrank2
            (by rw [hpp, pActList_snoc]) (by simp) (fun i l e => by
              have h := List.append_inj' e rfl
              simp only [List.cons.injEq, and_true] at h
              rw [h.2])
            hrs' (by
              constructor
              · intro hh; exact ⟨p, m, rfl, by simpa using hh⟩
              · rintro ⟨i, l, e, hl⟩
                have := List.append_inj' e rfl
                simp only [List.cons.injEq, and_true] at this
                rw [this.2]; simpa using hl)
            (by rw [hsg, sigOf_snoc])
            (by rw [hlen]; exact hrec) q' hq' (by simpa using hadj) (by simpa using hcan) (by simp)
            (by simpa using hlast) s2 hs2 (by simpa using hsol) (by simpa using hmx)
            (by intro i l e; exact hord i l (by simpa using e)) (by simpa using hsig)
          simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
          omega

/-- **The superflip with all centres at home needs 22 face turns on the supercube.** -/
theorem supercube_superflip (w : List Nat) (hw : ∀ m ∈ w, m < 18) (h : eval w = sfSt) (hz : sigOf w = sig0) :
    22 ≤ w.length := by
  rcases Nat.lt_or_ge w.length 22 with hlt | hge
  · exfalso
    obtain ⟨s1, s2, hsol, hlen, hs2, hhead, hlast, hadj, hadjAll, hcan1, hcan2, hrun⟩ :=
      normal_formZ w ⟨⟨hw, h⟩, Z_of_sig hw hz⟩ (by omega)
    have hall : ∀ m ∈ s1 ++ s2, m < 18 := hsol.1.1
    have hs1 : ∀ m ∈ s1, m < 18 := fun m hm => hall m (by simp [hm])
    have hs2g : ∀ m ∈ s2, m ∈ g2Moves := fun m hm => List.contains_iff_mem.1 (hs2 m hm)
    have hsolA : applyList sfSt (([] ++ s1) ++ s2) = St.id := by
      rw [List.nil_append]; exact (sol_iff hall).2 hsol.1.2
    have root := sc_true
    unfold scF at root
    have := sc_spec 21 [] (rank sfSt) (rank sfSt) (rank sfSt) idP 6 run0 false sig0 (by simp) (by simp) rfl rfl rfl rfl
      (fun _ => rfl) (fun i l e => by simp at e) rfl (by simp) rfl root s1 hs1 (by simpa using hadj)
      (by simpa using hcan1) (fun _ => hhead) (by simpa using hlast) s2 hs2g hsolA (by simpa using hrun)
      (by
        intro i l e
        simp only [List.nil_append] at e
        rw [e] at hadjAll
        exact ordH_of i l hadjAll hcan2)
      (by simpa using sig_of_Z hall hsol.2)
    simp only [List.length_nil, Nat.zero_add] at this
    simp only [List.length_append] at hlen
    omega
  · exact hge

#print axioms supercube_superflip
