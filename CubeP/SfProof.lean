import CubeP.SfNorm
import CubeP.SfThm
open Std

/-! **The superflip needs 20 face turns.** With `upper_bound_28` this gives a machine-checked
20 ≤ God's number ≤ 28 (half-turn metric). -/

theorem allLt_spec (f : Nat → Bool) : ∀ n, allLt f n = true → ∀ m < n, f m = true := by
  intro n
  induction n with
  | zero => intro _ m hm; omega
  | succ n ih =>
    intro h m hm
    have e : allLt f (n + 1) = if f n then allLt f n else false := rfl
    rw [e] at h
    by_cases hc : f n = true
    · rw [if_pos hc] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h' | h'
      · exact ih h m h'
      · rw [h']; exact hc
    · rw [if_neg hc] at h; exact absurd h (by simp)

theorem sfSearch_zero (d1 d2 : ByteArray) (r0 r1 r2 : Nat) (p : P) (g lastf : Nat) (rs : RunSt) (lnh : Bool) :
    sfSearch d1 d2 0 r0 r1 r2 p g lastf rs lnh =
      ((!(lnh && (d1.get! r0).toNat == 0) || decide (20 ≤ g + max rs.mx (d2.get! (cellOf p)).toNat)) && true) := rfl

theorem sfSearch_succ (d1 d2 : ByteArray) (f r0 r1 r2 : Nat) (p : P) (g lastf : Nat) (rs : RunSt) (lnh : Bool) :
    sfSearch d1 d2 (f + 1) r0 r1 r2 p g lastf rs lnh =
      ((!(lnh && (d1.get! r0).toNat == 0) || decide (20 ≤ g + max rs.mx (d2.get! (cellOf p)).toNat)) &&
       allLt (fun m =>
         m / 3 == lastf || (g == 0 && !(m == 3 || m == 5)) ||
         (decide (19 < g + 1 + (d1.get! (next r0 m)).toNat + (runStep rs m).mx) ||
          decide (19 < g + 1 + (d1.get! (next r1 (muS m))).toNat) ||
          decide (19 < g + 1 + (d1.get! (next r2 (muS (muS m)))).toNat) ||
          sfSearch d1 d2 f (next r0 m) (next r1 (muS m)) (next r2 (muS (muS m))) (pAct p m) (g + 1) (m / 3)
            (runStep rs m) (!isHUD m))) 18) := rfl

theorem pActList_snoc (p : P) (w : List Nat) (m : Nat) : pActList p (w ++ [m]) = pAct (pActList p w) m := by
  unfold pActList; rw [List.foldl_append]; rfl

theorem muS_lt {m : Nat} (hm : m < 18) : muS m < 18 := (norm_parts.1.mv m hm).1

theorem inC_sf (w : List Nat) (hw : ∀ m ∈ w, m < 18) : InC (applyList sfSt w) := by
  rw [← sf_parts.2.2.1]
  show InC (applyList (applyList St.id superflip) w)
  rw [← applyList_append]
  exact inC_applyList _ (all_append sf_parts.2.2.2.1 hw) St.id inC_id

theorem rank_id : rank St.id = i0 := rfl

/-- lower bound from the phase-1 table along any axis: a word solving the superflip after a prefix needs at least
the table value of the prefix position -/
theorem d1_bound {u v : List Nat} (hu : ∀ m ∈ u, m < 18) (hv : ∀ m ∈ v, m < 18)
    (h : applyList sfSt (u ++ v) = St.id) :
    ((distF ()).get! (rank (applyList sfSt u))).toNat ≤ v.length := by
  have := lip_reach v hv _ (inC_sf u hu)
  rw [← applyList_append, h, rank_id, low_parts.2.1] at this
  omega

theorem sol_mapS {w : List Nat} (hw : ∀ m ∈ w, m < 18) (h : applyList sfSt w = St.id) :
    applyList sfSt (w.map muS) = St.id := by
  have hS := norm_parts.1
  have hw' : ∀ m ∈ w.map muS, m < 18 := map_lt (fun m hm => (hS.mv m hm).1) hw
  exact (sol_iff hw').2 (sol_cj hS hw ((sol_iff hw).1 h))

/-- at a leaf (the prefix ends in ⟨U,D,R2,L2,F2,B2⟩-form), the rest is bounded by the exact phase-2 distance -/
theorem leaf_bound {p : List Nat} (hp : ∀ m ∈ p, m < 18) {s2 : List Nat} (hs2 : ∀ m ∈ s2, m ∈ g2Moves)
    (hsol : applyList sfSt (p ++ s2) = St.id) :
    rank (applyList sfSt p) = i0 ∧ ((dist2F ()).get! (cellOf (pActList idP p))).toNat ≤ s2.length := by
  have Vx := valid_applyList p hp sfSt sfValid
  rw [applyList_append] at hsol
  obtain ⟨hrk, hdom⟩ := hform_of_solved Vx hs2 hsol
  refine ⟨hrk, ?_⟩
  have e1 : pActList idP p = ((applyList sfSt p).cp, (applyList sfSt p).ep) := (applyList_pact p sfSt).symm
  have := lip2_reach s2 hs2 _ hdom
  rw [← applyList_pact, hsol] at this
  have e2 : cellOf ((St.id).cp, (St.id).ep) = idCell := rfl
  rw [e2, low2_parts.2.1] at this
  rw [e1]; omega

theorem leaf_case {p : List Nat} (hp : ∀ m ∈ p, m < 18) {rs : RunSt} (hrs : rs = runOf p) {lnh : Bool}
    (hlnh : lnh = true ↔ ∃ i l, p = i ++ [l] ∧ isHUD l = false)
    (hA : (!(lnh && ((distF ()).get! (rank (applyList sfSt p))).toNat == 0) ||
      decide (20 ≤ p.length + max rs.mx ((dist2F ()).get! (cellOf (pActList idP p))).toNat)) = true)
    (hlast : ∃ i l, p ++ [] = i ++ [l] ∧ isHUD l = false)
    {s2 : List Nat} (hs2 : ∀ m ∈ s2, m ∈ g2Moves) (hsol : applyList sfSt ((p ++ []) ++ s2) = St.id)
    (hmx : (runOf (p ++ [])).mx ≤ s2.length) : 20 ≤ p.length + ([] : List Nat).length + s2.length := by
  simp only [List.append_nil] at hlast hsol hmx
  obtain ⟨hrk, hd2⟩ := leaf_bound hp hs2 hsol
  have hl : lnh = true := hlnh.2 hlast
  rw [hrk, low_parts.2.1, hl] at hA
  simp only [Bool.true_and, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hA
  rw [hrs] at hA
  simp only [List.length_nil, Nat.add_zero]
  have := Nat.max_le.2 ⟨hmx, hd2⟩
  omega

/-- **Specification of the search.** -/
theorem sf_spec : ∀ (f : Nat) (p : List Nat) (r0 r1 r2 : Nat) (pp : P) (lastf : Nat) (rs : RunSt) (lnh : Bool),
    f + p.length = 19 → (∀ m ∈ p, m < 18) →
    r0 = rank (applyList sfSt p) → r1 = rank (applyList sfSt (p.map muS)) →
    r2 = rank (applyList sfSt ((p.map muS).map muS)) → pp = pActList idP p →
    (p = [] → lastf = 6) → (∀ i l, p = i ++ [l] → lastf = l / 3) → rs = runOf p →
    (lnh = true ↔ ∃ i l, p = i ++ [l] ∧ isHUD l = false) →
    sfSearch (distF ()) (dist2F ()) f r0 r1 r2 pp p.length lastf rs lnh = true →
    ∀ q : List Nat, (∀ m ∈ q, m < 18) → NoAdj (p ++ q) → (p = [] → ∃ x t, q = x :: t ∧ (x = 3 ∨ x = 5)) →
      (∃ i l, p ++ q = i ++ [l] ∧ isHUD l = false) →
      ∀ s2 : List Nat, (∀ m ∈ s2, m ∈ g2Moves) → applyList sfSt ((p ++ q) ++ s2) = St.id →
        (runOf (p ++ q)).mx ≤ s2.length → 20 ≤ p.length + q.length + s2.length := by
  intro f
  induction f with
  | zero =>
    intro p r0 r1 r2 pp lastf rs lnh hf hp hr0 hr1 hr2 hpp hl0 hl1 hrs hlnh hs q hq hadj hhead hlast s2 hs2 hsol hmx
    cases q with
    | cons m q' => simp; omega
    | nil =>
      rw [sfSearch_zero, Bool.and_true] at hs
      subst hr0 hpp
      exact leaf_case hp hrs hlnh hs hlast hs2 hsol hmx
  | succ f ih =>
    intro p r0 r1 r2 pp lastf rs lnh hf hp hr0 hr1 hr2 hpp hl0 hl1 hrs hlnh hs q hq hadj hhead hlast s2 hs2 hsol hmx
    rw [sfSearch_succ, Bool.and_eq_true] at hs
    obtain ⟨hA, hB⟩ := hs
    cases q with
    | nil =>
      subst hr0 hpp
      exact leaf_case hp hrs hlnh hA hlast hs2 hsol hmx
    | cons m q' =>
      have hm18 : m < 18 := hq m (by simp)
      have hq' : ∀ k ∈ q', k < 18 := fun k hk => hq k (by simp [hk])
      have hpm : ∀ k ∈ p ++ [m], k < 18 := all_append hp (by simp [hm18])
      have hall : ∀ k ∈ p ++ m :: q', k < 18 := all_append hp hq
      have hs2' : ∀ k ∈ s2, k < 18 := fun k hk => g2_lt (hs2 k hk)
      have hc := allLt_spec _ 18 hB m hm18
      simp only at hc
      rw [Bool.or_eq_true, Bool.or_eq_true] at hc
      rcases hc with (hface | hfirst) | hrest
      · -- consecutive moves on one face: excluded
        exfalso
        have hf' : m / 3 = lastf := by simpa using hface
        cases hrev : p.reverse with
        | nil =>
          have hp0 : p = [] := List.reverse_eq_nil_iff.1 hrev
          have := hl0 hp0; omega
        | cons l t =>
          have hil : p = t.reverse ++ [l] := by rw [← List.reverse_reverse p, hrev]; simp
          have hlf := hl1 _ _ hil
          exact hadj t.reverse q' l m (by rw [hil]; simp) (by omega)
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
        -- facts about the full solution
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
        · -- pruned by the phase-1 table on the U-D axis and the run bound
          have h0' := of_decide_eq_true h0
          rw [hrank0, hrs'] at h0'
          have hlip := lip_reach q' hq' _ (inC_sf _ hpm)
          rw [← applyList_append, List.append_assoc, List.singleton_append, hleaf, low_parts.2.1] at hlip
          simp only [List.length_cons]
          omega
        · -- pruned by the phase-1 table on the second axis
          have h1' := of_decide_eq_true h1
          rw [hrank1] at h1'
          have hs := sol_mapS (all_append hall hs2') hsolL
          have e : (p ++ m :: q' ++ s2).map muS = (p ++ [m]).map muS ++ (q' ++ s2).map muS := by simp
          rw [e] at hs
          have := d1_bound (map_lt (μ := muS) (fun k hk => muS_lt hk) hpm)
            (map_lt (μ := muS) (fun k hk => muS_lt hk) (all_append hq' hs2')) hs
          simp only [List.length_map, List.length_append] at this
          simp only [List.length_cons]
          omega
        · -- pruned by the phase-1 table on the third axis
          have h2' := of_decide_eq_true h2
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
        · -- recurse
          have hlen : (p ++ [m]).length = p.length + 1 := by simp
          have := ih (p ++ [m]) (next r0 m) (next r1 (muS m)) (next r2 (muS (muS m))) (pAct pp m) (m / 3) (runStep rs m)
            (!isHUD m) (by rw [hlen]; omega) hpm hrank0 hrank1 hrank2
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
            (by rw [hlen]; exact hrec) q' hq' (by simpa using hadj) (by simp) (by simpa using hlast) s2 hs2
            (by simpa using hsol) (by simpa using hmx)
          simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
          omega

/-- **The superflip needs 20 face turns.** No word of fewer than 20 face turns solves the superflip. -/
theorem superflip_lower (w : List Nat) (hw : ∀ m ∈ w, m < 18) (h : applyList (eval superflip) w = St.id) :
    20 ≤ w.length := by
  rw [sf_parts.2.2.1] at h
  have hev : eval w = sfSt := (sol_iff hw).1 h
  rcases Nat.lt_or_ge w.length 20 with hlt | hge
  · exfalso
    obtain ⟨s1, s2, hsol, hlen, hs2, hhead, hlast, hadj, hrun⟩ := normal_form w ⟨hw, hev⟩ (by omega)
    have hall : ∀ m ∈ s1 ++ s2, m < 18 := hsol.1
    have hs1 : ∀ m ∈ s1, m < 18 := fun m hm => hall m (by simp [hm])
    have hs2g : ∀ m ∈ s2, m ∈ g2Moves := fun m hm => List.contains_iff_mem.1 (hs2 m hm)
    have hsolA : applyList sfSt (([] ++ s1) ++ s2) = St.id := by
      rw [List.nil_append]; exact (sol_iff hall).2 hsol.2
    have root := sf_true
    unfold sfF at root
    have := sf_spec 19 [] (rank sfSt) (rank sfSt) (rank sfSt) idP 6 run0 false (by simp) (by simp) rfl rfl rfl rfl
      (fun _ => rfl) (fun i l e => by simp at e) rfl (by simp) root s1 hs1 (by simpa using hadj) (fun _ => hhead)
      (by simpa using hlast) s2 hs2g hsolA (by simpa using hrun)
    simp only [List.length_nil, Nat.zero_add] at this
    simp only [List.length_append] at hlen
    omega
  · exact hge

/-- **The superflip is at distance exactly 20** (Reid 1995), machine-checked. -/
theorem superflip_distance :
    (∀ w, (∀ m ∈ w, m < 18) → applyList (eval superflip) w = St.id → 20 ≤ w.length) ∧
    (∀ m ∈ superflip, m < 18) ∧ superflip.length = 20 ∧ applyList (eval superflip) superflip = St.id := by
  refine ⟨superflip_lower, sf_parts.2.2.2.1, sf_parts.2.2.2.2.1, ?_⟩
  rw [sf_parts.2.2.1]
  exact (sol_iff sf_parts.2.2.2.1).2 sf_parts.2.2.1

/-- **20 ≤ God's number ≤ 28** (half-turn metric): every position is solved in at most 28 face turns, and the
superflip needs 20. -/
theorem gods_number_bounds :
    (∀ w, (∀ m ∈ w, m < 18) → ∃ W : List Nat, W.length ≤ 28 ∧ (∀ m ∈ W, m < 18) ∧ applyList (eval w) W = St.id) ∧
    (∃ w, (∀ m ∈ w, m < 18) ∧
      ∀ W, (∀ m ∈ W, m < 18) → applyList (eval w) W = St.id → 20 ≤ W.length) :=
  ⟨upper_bound_28, superflip, sf_parts.2.2.2.1, superflip_lower⟩

#print axioms superflip_distance
#print axioms gods_number_bounds
