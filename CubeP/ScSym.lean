import CubeP.ScNorm
open Std

/-! Two more symmetries for the supercube normal form.
* The mirror in the plane between F and B (`mirS`): it is not a rotation, so it is not conjugation by a cube state;
  it acts on the arrays directly (positions reflected, corner twists negated). It sends R' to R, U to U', F to B', ...
  and negates every centre count, so it keeps "superflip with all centres at home".
* The half turn x2 about the R–L axis: a rotation (conjugation by `X2st`), fixing R and L, swapping U↔D and F↔B.
With them a least-key normal form starts with R, its second face is U, F or L, and after R L its third face is U or F
(`symOK`). -/

-- ---------- the F–B mirror ----------
def sigC : Array Nat := #[3, 2, 1, 0, 7, 6, 5, 4]
def sigE : Array Nat := #[0, 3, 2, 1, 4, 7, 6, 5, 11, 10, 9, 8]

def mirS (x : St) : St :=
  ⟨(List.range 8).toArray.map (fun i => sigC[x.cp[sigC[i]!]!]!),
   (List.range 8).toArray.map (fun i => (3 - x.co[sigC[i]!]!) % 3),
   (List.range 12).toArray.map (fun i => sigE[x.ep[sigE[i]!]!]!),
   (List.range 12).toArray.map (fun i => x.eo[sigE[i]!]!)⟩

/-- face permutation of the mirror (F ↔ B) -/
def piF : Array Nat := #[0, 1, 5, 3, 4, 2]
def muMArr : Array Nat := (List.range 18).toArray.map (fun m => 3 * piF[m / 3]! + (2 - m % 3))
def muM (m : Nat) : Nat := muMArr[m]!

theorem sigC_facts : ∀ i < 8, sigC[i]! < 8 ∧ sigC[sigC[i]!]! = i := by decide
theorem sigE_facts : ∀ i < 12, sigE[i]! < 12 ∧ sigE[sigE[i]!]! = i := by decide

theorem mir_moves : ∀ m < 18, muM m < 18 ∧ mirS moves[m]! = moves[muM m]! := by native_decide
theorem mir_sf : mirS sfSt = sfSt := by native_decide
theorem mir_id : mirS St.id = St.id := by native_decide
theorem muM_facts : ∀ m < 18, isHUD (muM m) = isHUD m ∧ muM m % 3 = 2 - m % 3 ∧ m % 3 < 3 := by native_decide
theorem muM_face : ∀ g < 6, ∀ m < 18, (muM m / 3 = g ↔ m / 3 = piF[g]!) := by native_decide
theorem piF_lt : ∀ g < 6, piF[g]! < 6 := by decide
theorem muM_5 : muM 5 = 3 := by native_decide

theorem mirS_cp (x : St) : (mirS x).cp = (List.range 8).toArray.map (fun i => sigC[x.cp[sigC[i]!]!]!) := rfl
theorem mirS_co (x : St) : (mirS x).co = (List.range 8).toArray.map (fun i => (3 - x.co[sigC[i]!]!) % 3) := rfl
theorem mirS_ep (x : St) : (mirS x).ep = (List.range 12).toArray.map (fun i => sigE[x.ep[sigE[i]!]!]!) := rfl
theorem mirS_eo (x : St) : (mirS x).eo = (List.range 12).toArray.map (fun i => x.eo[sigE[i]!]!) := rfl

theorem valid_mirS {x : St} (hx : Valid x) : Valid (mirS x) := by
  obtain ⟨-, -, -, -, x5, x6, x7, x8⟩ := hx
  refine ⟨by rw [mirS_cp]; simp, by rw [mirS_co]; simp, by rw [mirS_ep]; simp, by rw [mirS_eo]; simp, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [mirS_cp, gmr hi]; exact (sigC_facts _ (x5 _ (sigC_facts i hi).1)).1
  · intro i hi
    rw [mirS_co, gmr hi]; exact Nat.mod_lt _ (by decide)
  · intro i hi
    rw [mirS_ep, gmr hi]; exact (sigE_facts _ (x7 _ (sigE_facts i hi).1)).1
  · intro i hi
    rw [mirS_eo, gmr hi]; exact x8 _ (sigE_facts i hi).1

theorem mirS_mul {x y : St} (hx : Valid x) (hy : Valid y) : mirS (x.mul y) = (mirS x).mul (mirS y) := by
  obtain ⟨-, -, -, -, x5, x6, x7, x8⟩ := hx
  obtain ⟨-, -, -, -, y5, y6, y7, y8⟩ := hy
  apply St.ext'
  · rw [mirS_cp, mul_cp, mul_cp, mirS_cp, mirS_cp]
    apply map_range_congr; intro i hi
    have hs := (sigC_facts i hi).1
    have hy' := y5 _ hs
    rw [gmr hs, gmr hi, gmr (sigC_facts _ hy').1, (sigC_facts _ hy').2]
  · rw [mirS_co, mul_co, mul_co, mirS_co, mirS_co, mirS_cp]
    apply map_range_congr; intro i hi
    have hs := (sigC_facts i hi).1
    have hy' := y5 _ hs
    rw [gmr hs, gmr hi, gmr hi, gmr (sigC_facts _ hy').1, (sigC_facts _ hy').2]
    have a1 := x6 _ hy'
    have a2 := y6 _ hs
    omega
  · rw [mirS_ep, mul_ep, mul_ep, mirS_ep, mirS_ep]
    apply map_range_congr; intro i hi
    have hs := (sigE_facts i hi).1
    have hy' := y7 _ hs
    rw [gmr hs, gmr hi, gmr (sigE_facts _ hy').1, (sigE_facts _ hy').2]
  · rw [mirS_eo, mul_eo, mul_eo, mirS_eo, mirS_eo, mirS_ep]
    apply map_range_congr; intro i hi
    have hs := (sigE_facts i hi).1
    have hy' := y7 _ hs
    rw [gmr hs, gmr hi, gmr hi, gmr (sigE_facts _ hy').1, (sigE_facts _ hy').2]

theorem mirS_eval : ∀ w : List Nat, (∀ m ∈ w, m < 18) → mirS (eval w) = eval (w.map muM) := by
  intro w
  induction w with
  | nil => intro _; exact mir_id
  | cons m w ih =>
    intro hw
    have hm := hw m (by simp)
    have hw' : ∀ k ∈ w, k < 18 := fun k hk => hw k (by simp [hk])
    have hμ : ∀ k ∈ w.map muM, k < 18 := map_lt (fun k hk => (mir_moves k hk).1) hw'
    rw [eval_cons hm hw', mirS_mul (move_facts hm).1 (valid_eval w hw'), ih hw', List.map_cons,
      eval_cons (mir_moves m hm).1 hμ, (mir_moves m hm).2]

theorem cnt_mir : ∀ w : List Nat, (∀ m ∈ w, m < 18) → ∀ g < 6, (cnt g (w.map muM) + cnt (piF[g]!) w) % 4 = 0 := by
  intro w
  induction w with
  | nil => intro _ g _; rfl
  | cons m t ih =>
    intro hw g hg
    have hm := hw m (by simp)
    have ih' := ih (fun k hk => hw k (by simp [hk])) g hg
    have hf := muM_face g hg m hm
    obtain ⟨-, h2, h3⟩ := muM_facts m hm
    simp only [List.map_cons, cnt]
    by_cases hc : m / 3 = piF[g]!
    · rw [if_pos (hf.2 hc), if_pos hc]; omega
    · rw [if_neg (fun e => hc (hf.1 e)), if_neg hc]; omega

theorem isSolZ_mir {w : List Nat} (h : IsSolZ w) : IsSolZ (w.map muM) := by
  have hw := h.1.1
  have hl : ∀ k ∈ w.map muM, k < 18 := map_lt (fun k hk => (mir_moves k hk).1) hw
  refine ⟨⟨hl, ?_⟩, ?_⟩
  · rw [← mirS_eval w hw, h.1.2, mir_sf]
  · intro g
    rcases Nat.lt_or_ge g 6 with hg | hg
    · have := cnt_mir w hw g hg
      have := h.2 (piF[g]!)
      omega
    · rw [cnt_ge6 hg _ hl]

-- ---------- the half turn x2 ----------
def X2st : St := (Yst.mul Z2st).mul Yist
def muXArr : Array Nat := #[9, 10, 11, 3, 4, 5, 15, 16, 17, 0, 1, 2, 12, 13, 14, 6, 7, 8]
def xF : Array Nat := #[3, 1, 5, 0, 4, 2]

theorem x2_rot : RotOK X2st X2st (fun m => muXArr[m]!) := rotOK_of (by native_decide)
theorem muX_facts : ∀ m < 18, muXArr[m]! < 18 ∧ muXArr[m]! % 3 = m % 3 ∧ isHUD muXArr[m]! = isHUD m := by
  native_decide
theorem muX_face : ∀ f < 6, ∀ m < 18, (muXArr[m]! / 3 = f ↔ m / 3 = xF[f]!) := by native_decide
theorem muX_3 : muXArr[3]! = 3 := by decide
theorem muX_L : ∀ m < 18, m / 3 = 4 → muXArr[m]! = m := by decide
theorem muX_DB : ∀ m < 18, (m / 3 = 3 ∨ m / 3 = 5) → (muXArr[m]! / 3 = 0 ∨ muXArr[m]! / 3 = 2) := by decide

theorem isSolZ_x2 {w : List Nat} (h : IsSolZ w) : IsSolZ (w.map (fun m => muXArr[m]!)) := by
  have hw := h.1.1
  refine ⟨isSol_map x2_rot h.1, ?_⟩
  intro f
  rcases Nat.lt_or_ge f 6 with hf | hf
  · rw [cnt_map (μ := fun m => muXArr[m]!) (fun m hm => (muX_facts m hm).2.1) (muX_face f hf) w hw]
    exact h.2 _
  · rw [cnt_ge6 hf _ (map_lt (fun m hm => (muX_facts m hm).1) hw)]

-- ---------- maps that keep ⟨U,D,R2,L2,F2,B2⟩ keep the H-tail ----------
theorem tH_keep {μ : Nat → Nat} (hμ : ∀ m < 18, isHUD (μ m) = isHUD m) {w : List Nat} (hw : ∀ m ∈ w, m < 18) :
    tH isHUD (w.map μ) = tH isHUD w := by
  rw [← tH_map]; unfold tH
  have : ∀ L : List Nat, (∀ m ∈ L, m < 18) → tRev (fun m => isHUD (μ m)) L = tRev isHUD L := by
    intro L hL
    induction L with
    | nil => rfl
    | cons m t ih =>
      have e1 := hμ m (hL m (by simp))
      have e2 := ih (fun k hk => hL k (by simp [hk]))
      simp only [tRev, e1, e2]
  exact this _ (fun m hm => hw m (List.mem_reverse.1 hm))

-- ---------- the key ----------
theorem keyR_lt_pow : ∀ u : List Nat, (∀ m ∈ u, m < 18) → keyR u < 6 ^ u.length := by
  intro u
  induction u with
  | nil => intro _; simp [keyR]
  | cons m t ih =>
    intro h
    have hm := h m (by simp)
    have := ih (fun k hk => h k (by simp [hk]))
    simp only [keyR, List.length_cons, Nat.pow_succ]
    have h5 : m / 3 ≤ 5 := by omega
    have : (m / 3) * 6 ^ t.length ≤ 5 * 6 ^ t.length := Nat.mul_le_mul_right _ h5
    omega

theorem keyR_head_lt {a b : Nat} {u v : List Nat} (hab : a / 3 < b / 3) (hl : u.length = v.length)
    (hu : ∀ m ∈ u, m < 18) : keyR (a :: u) < keyR (b :: v) := by
  simp only [keyR]
  have h1 := keyR_lt_pow u hu
  have h2 : (a / 3 + 1) * 6 ^ u.length ≤ (b / 3) * 6 ^ u.length := Nat.mul_le_mul_right _ hab
  rw [← hl]
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

theorem keyR_prefix_lt (p : List Nat) {u v : List Nat} (hl : u.length = v.length) (h : keyR u < keyR v) :
    keyR (p ++ u) < keyR (p ++ v) := by
  rw [keyR_app, keyR_app, hl]; omega

-- ---------- the normal form with symmetry restrictions ----------
/-- face of the last move of a prefix (6 for the empty prefix), as the search's `lastf` -/
def lastF (i : List Nat) : Nat :=
  match i.getLast? with
  | none => 6
  | some l => l / 3

theorem symOK_of {c : List Nat} (h1 : ∃ t, c = 3 :: t)
    (h2 : ∀ y t, c = 3 :: y :: t → y / 3 = 0 ∨ y / 3 = 2 ∨ y / 3 = 4)
    (h3 : ∀ y z t, c = 3 :: y :: z :: t → y / 3 = 4 → z / 3 = 0 ∨ z / 3 = 2) :
    ∀ i m r, c = i ++ m :: r → symOK i.length (lastF i) m = true := by
  intro i m r e
  obtain ⟨t, ht⟩ := h1
  match i, e with
  | [], e =>
    simp only [List.nil_append] at e
    rw [ht] at e; simp only [List.cons.injEq] at e
    simp [symOK, ← e.1]
  | [a], e =>
    rw [ht] at e; simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have := h2 m r (by rw [ht])
    simp only [symOK, List.length_singleton]
    rcases this with h | h | h <;> simp [h]
  | [a, b], e =>
    rw [ht] at e; simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    simp only [symOK, lastF, List.length_cons, List.length_nil, List.getLast?_cons_cons, List.getLast?_singleton]
    by_cases hb : b / 3 = 4
    · have := h3 b m r (by rw [ht]) hb
      rcases this with h | h <;> simp [hb, h]
    · simp [hb]
  | a :: b :: c :: i', _ =>
    simp [symOK]

/-- **Normal form with symmetry restrictions.** As `normal_formZ`, and moreover the word starts with R, its second
face is U, F or L, and after R L the third face is U or F. -/
theorem normal_formZ2 (w0 : List Nat) (hw0 : IsSolZ w0) (hl0 : w0.length ≤ 21) :
    ∃ s1 s2 : List Nat, IsSolZ (s1 ++ s2) ∧ (s1 ++ s2).length ≤ 21 ∧ (∀ m ∈ s2, isHUD m = true) ∧
      (∃ t, s1 = 3 :: t) ∧ (∃ i l, s1 = i ++ [l] ∧ isHUD l = false) ∧ NoAdj s1 ∧
      NoAdj (s1 ++ s2) ∧ Canon s1 ∧ Canon s2 ∧ (runOf s1).mx ≤ s2.length ∧
      (∀ i m r, s1 ++ s2 = i ++ m :: r → symOK i.length (lastF i) m = true) := by
  obtain ⟨n, ⟨w1, hw1, hw1l⟩, hminP⟩ := exists_least (P := fun n => ∃ w, IsSolZ w ∧ w.length = n) _ _
    (Nat.le_refl _) ⟨w0, hw0, rfl⟩
  have hmin : ∀ w, IsSolZ w → n ≤ w.length := fun w hw => hminP _ ⟨w, hw, rfl⟩
  have hn : n ≤ 21 := Nat.le_trans (hmin w0 hw0) hl0
  obtain ⟨k0, ⟨c, hc, hcn, hck⟩, hk0⟩ :=
    exists_least (P := fun k => ∃ w, IsSolZ w ∧ w.length = n ∧ tH isHUD w + k = n) _ _ (Nat.le_refl _)
      ⟨w1, hw1, hw1l, (by have := tH_le isHUD w1; omega : tH isHUD w1 + (n - tH isHUD w1) = n)⟩
  have hmax : ∀ w, IsSolZ w → w.length = n → tH isHUD w ≤ tH isHUD c := by
    intro w hw hwl
    rcases Nat.lt_or_ge (tH isHUD c) (tH isHUD w) with hlt | hge
    · exfalso
      have := hk0 (n - tH isHUD w) ⟨w, hw, hwl, (by have := tH_le isHUD w; omega)⟩
      have h2 := tH_le isHUD w
      omega
    · exact hge
  obtain ⟨c1, hc1, hc1n, hc1t, t1, hc1h⟩ := first_RR hmin hc hcn hmax
  -- a maximal word starting with R (mirror if it starts with R')
  have hR : ∃ c1', IsSolZ c1' ∧ c1'.length = n ∧ tH isHUD c1' = tH isHUD c ∧ ∃ t, c1' = 3 :: t := by
    rcases hc1h with h | h
    · exact ⟨c1, hc1, hc1n, hc1t, t1, h⟩
    · refine ⟨c1.map muM, isSolZ_mir hc1, by simp [hc1n], ?_, t1.map muM, ?_⟩
      · rw [tH_keep (fun m hm => (muM_facts m hm).1) hc1.1.1]; exact hc1t
      · rw [h, List.map_cons, muM_5]
  obtain ⟨c1', hc1', hc1n', hc1t', hc1h'⟩ := hR
  -- a word of least key among the maximal words starting with R
  obtain ⟨kk, ⟨c2, hc2, hc2n, hc2t, hc2h, hc2k⟩, hkk⟩ :=
    exists_least (P := fun k => ∃ w, IsSolZ w ∧ w.length = n ∧ tH isHUD w = tH isHUD c ∧
        (∃ t, w = 3 :: t) ∧ keyR w = k) _ _ (Nat.le_refl _) ⟨c1', hc1', hc1n', hc1t', hc1h', rfl⟩
  have hmax2 : ∀ w, IsSolZ w → w.length = n → tH isHUD w ≤ tH isHUD c2 := by
    intro w hw hwl; rw [hc2t]; exact hmax w hw hwl
  let L := c2.reverse
  let r := tH isHUD c2
  have hsp := tRev_split isHUD L
  let s2 := (L.take r).reverse
  let s1 := (L.drop r).reverse
  have hsplit : c2 = s1 ++ s2 := by
    show c2 = (L.drop r).reverse ++ (L.take r).reverse
    rw [← List.reverse_append, List.take_append_drop, List.reverse_reverse]
  have hs2 : ∀ m ∈ s2, isHUD m = true := fun m hm => hsp.1 m (List.mem_reverse.1 hm)
  have hrL : r ≤ L.length := by
    show tH isHUD c2 ≤ c2.reverse.length
    rw [List.length_reverse]; exact tH_le isHUD c2
  have hlen : s2.length = r := by simp [s2]; omega
  obtain ⟨⟨x, t, hxt, hx⟩, hlast, hadj, hruns⟩ := max_propsZ hmin hc2 hc2n hmax2 hsplit hs2 hlen
  have hc2x : c2 = x :: (t ++ s2) := by rw [hsplit, hxt]; simp
  have hx3 : x = 3 := by
    obtain ⟨t', h⟩ := hc2h
    rw [hc2x] at h; simp only [List.cons.injEq] at h; exact h.1
  -- any candidate of smaller key is impossible
  have noswap : ∀ c3 : List Nat, IsSolZ c3 → c3.length = n → s2.length ≤ tH isHUD c3 →
      (∃ t, c3 = 3 :: t) → keyR c3 < keyR c2 → False := by
    intro c3 h3 h3n h3t h3h h3k
    have h3t' : tH isHUD c3 = tH isHUD c := by
      have := hmax c3 h3 h3n
      have e : s2.length = tH isHUD c := by rw [hlen]; exact hc2t
      omega
    have := hkk (keyR c3) ⟨c3, h3, h3n, h3t', h3h, rfl⟩
    omega
  have hadjAll : NoAdj c2 := by
    intro u v a b e hf
    obtain ⟨w, hw, hwl⟩ := isSolZ_merge (by rw [← e]; exact hc2) hf
    have := hmin w hw
    rw [← e, hc2n] at hwl
    omega
  -- the x2 image is a candidate
  have hx2cand : IsSolZ (c2.map (fun m => muXArr[m]!)) ∧ (c2.map (fun m => muXArr[m]!)).length = n ∧
      s2.length ≤ tH isHUD (c2.map (fun m => muXArr[m]!)) := by
    refine ⟨isSolZ_x2 hc2, by simp [hc2n], ?_⟩
    rw [tH_keep (fun m hm => (muX_facts m hm).2.2) hc2.1.1, hlen]; exact Nat.le_refl _
  have hall2 : ∀ m ∈ c2, m < 18 := hc2.1.1
  -- second face
  have hsecond : ∀ y t', c2 = 3 :: y :: t' → y / 3 = 0 ∨ y / 3 = 2 ∨ y / 3 = 4 := by
    intro y t' e
    have hy : y < 18 := hall2 y (by rw [e]; simp)
    have hy1 : y / 3 ≠ 1 := fun h => hadjAll [] t' 3 y (by rw [e]; rfl) (by omega)
    rcases (by omega : y / 3 = 0 ∨ y / 3 = 2 ∨ y / 3 = 4 ∨ y / 3 = 3 ∨ y / 3 = 5 ∨ y / 3 = 1) with
      h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    all_goals first | exact absurd h hy1 | skip
    all_goals
      exfalso
      obtain ⟨hA, hB, hC⟩ := hx2cand
      have hyx := muX_DB y hy (by omega)
      have ht' : ∀ m ∈ t', m < 18 := fun m hm => hall2 m (by rw [e]; simp [hm])
      apply noswap _ hA hB hC ⟨(y :: t').map (fun m => muXArr[m]!), by rw [e, List.map_cons, muX_3]⟩
      rw [e, List.map_cons, List.map_cons, muX_3]
      apply keyR_prefix_lt [3] (by simp)
      apply keyR_head_lt (by omega) (by simp) (map_lt (fun m hm => (muX_facts m hm).1) ht')
  -- third face after R L
  have hthird : ∀ y z t', c2 = 3 :: y :: z :: t' → y / 3 = 4 → z / 3 = 0 ∨ z / 3 = 2 := by
    intro y z t' e hy4
    have hy : y < 18 := hall2 y (by rw [e]; simp)
    have hz : z < 18 := hall2 z (by rw [e]; simp)
    have hz4 : z / 3 ≠ 4 := fun h => hadjAll [3] t' y z (by rw [e]; rfl) (by omega)
    have hz1 : z / 3 ≠ 1 := by
      intro hz1
      have hsw : IsSolZ ([3] ++ z :: y :: t') :=
        isSolZ_swap (u := [3]) (by rw [show [3] ++ y :: z :: t' = c2 by rw [e]; rfl]; exact hc2)
          (by omega) (by omega)
      have hsw' : IsSolZ ([] ++ 3 :: z :: (y :: t')) := by simpa using hsw
      obtain ⟨w, hw, hwl⟩ := isSolZ_merge hsw' (by omega)
      have := hmin w hw
      have hl : ([] ++ 3 :: z :: (y :: t')).length = n := by rw [← hc2n, e]; simp
      omega
    rcases (by omega : z / 3 = 0 ∨ z / 3 = 2 ∨ z / 3 = 3 ∨ z / 3 = 5 ∨ z / 3 = 1 ∨ z / 3 = 4) with
      h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    rotate_left 2
    · exact absurd h hz1
    · exact absurd h hz4
    all_goals
      exfalso
      obtain ⟨hA, hB, hC⟩ := hx2cand
      have hzx := muX_DB z hz (by omega)
      have ht' : ∀ m ∈ t', m < 18 := fun m hm => hall2 m (by rw [e]; simp [hm])
      apply noswap _ hA hB hC ⟨(y :: z :: t').map (fun m => muXArr[m]!), by rw [e, List.map_cons, muX_3]⟩
      rw [e, List.map_cons, List.map_cons, List.map_cons, muX_3, muX_L y hy hy4]
      apply keyR_prefix_lt [3, y] (by simp)
      apply keyR_head_lt (by omega) (by simp) (map_lt (fun m hm => (muX_facts m hm).1) ht')
  refine ⟨s1, s2, by rw [← hsplit]; exact hc2, by rw [← hsplit, hc2n]; exact hn, hs2, ⟨t, by rw [hxt, hx3]⟩, hlast,
    hadj, by rw [← hsplit]; exact hadjAll, ?_, ?_, runOf_mx_le _ _ hruns,
    by rw [← hsplit]; exact symOK_of (by rw [hc2x, hx3]; exact ⟨_, rfl⟩) hsecond hthird⟩
  · -- inside s1
    intro u v a b e ⟨hax, hlt⟩
    have hne : a / 3 ≠ b / 3 := by omega
    have hc2e : c2 = u ++ a :: b :: (v ++ s2) := by rw [hsplit, e]; simp
    have h3 : IsSolZ (u ++ b :: a :: (v ++ s2)) := isSolZ_swap (by rw [← hc2e]; exact hc2) hne hax.symm
    apply noswap _ h3
    · rw [← hc2n, hc2e]; simp
    · have := tH_all_suffix isHUD (u ++ b :: a :: v) s2 hs2
      simpa using this
    · cases u with
      | nil =>
        exfalso
        simp only [List.nil_append] at e
        rw [hxt] at e
        simp only [List.cons.injEq] at e
        rw [← e.1, hx3] at hlt hax
        omega
      | cons y u' =>
        obtain ⟨t', h⟩ := hc2h
        refine ⟨u' ++ b :: a :: (v ++ s2), ?_⟩
        rw [hc2e] at h; simp only [List.cons_append, List.cons.injEq] at h; simp [h.1]
    · rw [hc2e]; exact keyR_swap u (v ++ s2) hlt
  · -- inside s2
    intro u v a b e ⟨hax, hlt⟩
    have hne : a / 3 ≠ b / 3 := by omega
    have hc2e : c2 = (s1 ++ u) ++ a :: b :: v := by rw [hsplit, e]; simp
    have h3 : IsSolZ ((s1 ++ u) ++ b :: a :: v) := isSolZ_swap (by rw [← hc2e]; exact hc2) hne hax.symm
    apply noswap _ h3
    · rw [← hc2n, hc2e]; simp
    · have hall : ∀ m ∈ u ++ b :: a :: v, isHUD m = true := by
        intro m hm
        apply hs2
        rw [e]
        simp only [List.mem_append, List.mem_cons] at hm ⊢
        rcases hm with hm | hm | hm | hm
        · exact Or.inl hm
        · exact Or.inr (Or.inr (Or.inl hm))
        · exact Or.inr (Or.inl hm)
        · exact Or.inr (Or.inr (Or.inr hm))
      have := tH_all_suffix isHUD s1 (u ++ b :: a :: v) hall
      have hl2 : (u ++ b :: a :: v).length = s2.length := by rw [e]; simp
      rw [List.append_assoc]
      omega
    · refine ⟨t ++ u ++ b :: a :: v, ?_⟩
      rw [hxt, hx3]; simp
    · rw [hc2e]; exact keyR_swap (s1 ++ u) v hlt
