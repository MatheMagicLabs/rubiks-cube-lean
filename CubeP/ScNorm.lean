import CubeP.ScAlg
open Std

/-! Normal form of a shortest solution of the superflip on the supercube with all centres at home (every face
turned a multiple of 360°). As in `SfNorm`, plus: commuting moves on opposite faces stand in increasing face order
inside `s1` and inside `s2`. -/

def IsSolZ (w : List Nat) : Prop := IsSol w ∧ Z w

/-- no adjacent pair of moves on opposite faces in decreasing face order -/
def Canon (w : List Nat) : Prop := ∀ u v a b, w = u ++ a :: b :: v → ¬((b / 3) % 3 = (a / 3) % 3 ∧ b / 3 < a / 3)

theorem cnt_map {μ : Nat → Nat} {f g : Nat} (h1 : ∀ m < 18, μ m % 3 = m % 3)
    (h2 : ∀ m < 18, (μ m / 3 = f ↔ m / 3 = g)) : ∀ w : List Nat, (∀ m ∈ w, m < 18) → cnt f (w.map μ) = cnt g w := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons m t ih =>
    intro h
    have hm : m < 18 := h m (by simp)
    simp only [List.map_cons, cnt]
    rw [ih (fun k hk => h k (by simp [hk])), h1 m hm]
    by_cases hg : m / 3 = g
    · rw [if_pos ((h2 m hm).2 hg), if_pos hg]
    · rw [if_neg (fun e => hg ((h2 m hm).1 e)), if_neg hg]

theorem Z_map {μa : Array Nat} (hμ : μa ∈ [muSArr, muYArr, muYiArr, muZArr]) (hlt : ∀ m < 18, μa[m]! < 18)
    {w : List Nat} (hw : ∀ m ∈ w, m < 18) (h : Z w) : Z (w.map (fun m => μa[m]!)) := by
  obtain ⟨h1, h2⟩ := rot_face hμ
  intro f
  rcases Nat.lt_or_ge f 6 with hf | hf
  · obtain ⟨g, hg⟩ := h2 f hf
    rw [cnt_map (μ := fun m => μa[m]!) h1 hg w hw]; exact h g
  · rw [cnt_ge6 hf _ (map_lt hlt hw)]

theorem isSolZ_rot {a b : List Nat} (h : IsSolZ (a ++ b)) : IsSolZ (b ++ a) := ⟨isSol_rot h.1, Z_rot h.2⟩

theorem isSolZ_map {T Ti : St} {μa : Array Nat} (hT : RotOK T Ti (fun m => μa[m]!))
    (hμ : μa ∈ [muSArr, muYArr, muYiArr, muZArr]) {w : List Nat} (h : IsSolZ w) :
    IsSolZ (w.map (fun m => μa[m]!)) :=
  ⟨isSol_map hT h.1, Z_map hμ (fun m hm => (hT.mv m hm).1) h.1.1 h.2⟩

theorem merge_eval {a b : Nat} (ha : a < 18) (hb : b < 18) (hf : a / 3 = b / 3) :
    ((a % 3 + b % 3 + 1) % 4 = 3 → (moves[a]!).mul moves[b]! = St.id) ∧
    ((a % 3 + b % 3 + 1) % 4 ≠ 3 → mergeOf a b < 18 ∧ (moves[a]!).mul moves[b]! = moves[mergeOf a b]!) := by
  have h := normFacts_true; unfold normFactsB at h
  simp only [Bool.and_eq_true] at h
  have := lt_of_range_all (lt_of_range_all h.2 ha) hb
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  rcases this with h1 | h1
  · exact absurd hf h1
  · split at h1
    · rename_i hc
      refine ⟨fun _ => of_decide_eq_true (by simpa using h1), fun hn => absurd (by simpa using hc) hn⟩
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      refine ⟨fun e => absurd (by simp [e]) hc, fun _ => h1⟩

theorem eval_pair {u v : List Nat} {a b : Nat} (hu : ∀ k ∈ u, k < 18) (hv : ∀ k ∈ v, k < 18) (ha : a < 18)
    (hb : b < 18) : eval (u ++ a :: b :: v) = ((eval u).mul ((moves[a]!).mul moves[b]!)).mul (eval v) := by
  have hab : ∀ k ∈ [a, b], k < 18 := by simp [ha, hb]
  have e1 : u ++ a :: b :: v = (u ++ [a, b]) ++ v := by simp
  rw [e1, eval_app hv (all_append hu hab), eval_app hab hu, eval_cons ha (by simp [hb]),
    eval_cons hb (by simp), show eval ([] : List Nat) = St.id from rfl, mul_id (move_facts hb).1]

theorem isSolZ_merge {u v : List Nat} {a b : Nat} (h : IsSolZ (u ++ a :: b :: v)) (hf : a / 3 = b / 3) :
    ∃ w, IsSolZ w ∧ w.length < (u ++ a :: b :: v).length := by
  have hu : ∀ k ∈ u, k < 18 := fun k hk => h.1.1 k (by simp [hk])
  have hv : ∀ k ∈ v, k < 18 := fun k hk => h.1.1 k (by simp [hk])
  have ha : a < 18 := h.1.1 a (by simp)
  have hb : b < 18 := h.1.1 b (by simp)
  have e := eval_pair hu hv ha hb
  obtain ⟨hid, hmg⟩ := merge_eval ha hb hf
  by_cases h3 : (a % 3 + b % 3 + 1) % 4 = 3
  · refine ⟨u ++ v, ⟨⟨all_append hu hv, ?_⟩, ?_⟩, by simp; omega⟩
    · rw [eval_app hv hu, ← h.1.2, e, hid h3, mul_id (valid_eval u hu)]
    · intro f
      have := h.2 f
      rw [cnt_app] at this ⊢
      simp only [cnt] at this
      by_cases hfa : a / 3 = f
      · rw [if_pos hfa, if_pos (by omega : b / 3 = f)] at this; omega
      · rw [if_neg hfa, if_neg (by omega : ¬ b / 3 = f)] at this; omega
  · obtain ⟨hc18, hcm⟩ := hmg h3
    rcases merge_cnt ha hb hf with ⟨h3', -⟩ | ⟨-, hc3, hc1⟩
    · exact absurd h3' h3
    · have hcv : ∀ k ∈ mergeOf a b :: v, k < 18 := by
        intro k hk; simp at hk; rcases hk with rfl | hk; exact hc18; exact hv k hk
      refine ⟨u ++ mergeOf a b :: v, ⟨⟨all_append hu hcv, ?_⟩, ?_⟩, by simp⟩
      · rw [eval_app hcv hu, eval_cons hc18 hv, ← h.1.2, e, hcm, mul_assoc' _ (move_facts hc18).1 (valid_eval v hv)]
      · intro f
        have := h.2 f
        rw [cnt_app] at this ⊢
        simp only [cnt] at this ⊢
        by_cases hfa : a / 3 = f
        · rw [if_pos hfa, if_pos (by omega : b / 3 = f)] at this
          rw [if_pos (by omega : mergeOf a b / 3 = f)]; omega
        · rw [if_neg hfa, if_neg (by omega : ¬ b / 3 = f)] at this
          rw [if_neg (by omega : ¬ mergeOf a b / 3 = f)]; omega

theorem isSolZ_swap {u v : List Nat} {a b : Nat} (h : IsSolZ (u ++ a :: b :: v)) (hne : a / 3 ≠ b / 3)
    (hax : (a / 3) % 3 = (b / 3) % 3) : IsSolZ (u ++ b :: a :: v) := by
  have hu : ∀ k ∈ u, k < 18 := fun k hk => h.1.1 k (by simp [hk])
  have hv : ∀ k ∈ v, k < 18 := fun k hk => h.1.1 k (by simp [hk])
  have ha : a < 18 := h.1.1 a (by simp)
  have hb : b < 18 := h.1.1 b (by simp)
  refine ⟨⟨?_, ?_⟩, Z_swap h.2⟩
  · intro k hk
    simp only [List.mem_append, List.mem_cons] at hk
    rcases hk with hk | hk | hk | hk
    · exact hu k hk
    · rw [hk]; exact hb
    · rw [hk]; exact ha
    · exact hv k hk
  · rw [eval_pair hu hv hb ha, ← commute_fact ha hb hne hax, ← eval_pair hu hv ha hb]; exact h.1.2

-- ---------- lexicographic key on the face sequence ----------
def keyR : List Nat → Nat
  | [] => 0
  | m :: w => (m / 3) * 6 ^ w.length + keyR w

theorem keyR_app (u x : List Nat) : keyR (u ++ x) = keyR u * 6 ^ x.length + keyR x := by
  induction u with
  | nil => simp [keyR]
  | cons m t ih =>
    simp only [List.cons_append, keyR, ih, List.length_append, Nat.pow_add]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem keyR_swap (u v : List Nat) {a b : Nat} (h : b / 3 < a / 3) :
    keyR (u ++ b :: a :: v) < keyR (u ++ a :: b :: v) := by
  rw [keyR_app, keyR_app]
  have hk : keyR (b :: a :: v) < keyR (a :: b :: v) := by
    simp only [keyR, List.length_cons, Nat.pow_succ]
    have hP : 0 < 6 ^ v.length := Nat.pow_pos (by decide : 0 < 6)
    have h1 : (b / 3) * 6 ^ v.length < (a / 3) * 6 ^ v.length := Nat.mul_lt_mul_of_pos_right h hP
    have e1 : (b / 3) * (6 ^ v.length * 6) = 6 * ((b / 3) * 6 ^ v.length) := by
      rw [← Nat.mul_assoc, Nat.mul_comm _ 6]
    have e2 : (a / 3) * (6 ^ v.length * 6) = 6 * ((a / 3) * 6 ^ v.length) := by
      rw [← Nat.mul_assoc, Nat.mul_comm _ 6]
    rw [e1, e2]; omega
  simp only [List.length_cons]
  omega

-- ---------- properties of extremal words ----------
theorem max_propsZ {n : Nat} (hmin : ∀ w, IsSolZ w → n ≤ w.length) {c : List Nat} (hc : IsSolZ c) (hcn : c.length = n)
    (hmax : ∀ w, IsSolZ w → w.length = n → tH isHUD w ≤ tH isHUD c) {s1 s2 : List Nat} (hsplit : c = s1 ++ s2)
    (hs2 : ∀ m ∈ s2, isHUD m = true) (hlen : s2.length = tH isHUD c) :
    (∃ x t, s1 = x :: t ∧ isHUD x = false) ∧ (∃ i l, s1 = i ++ [l] ∧ isHUD l = false) ∧ NoAdj s1 ∧
      (∀ p p' : List Nat, s1 = p ++ p' → ∀ a < 3, tH (isHa a) p ≤ s2.length) := by
  have hne : s1 ≠ [] := by
    intro h0
    rw [h0, List.nil_append] at hsplit
    have := eo_of_H s2 hs2
    rw [← hsplit, hc.1.2] at this
    exact sf_eo_ne this
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨x, t, rfl⟩ : ∃ x t, s1 = x :: t := by
      cases s1 with
      | nil => exact absurd rfl hne
      | cons x t => exact ⟨x, t, rfl⟩
    refine ⟨x, t, rfl, ?_⟩
    cases hxv : isHUD x with
    | false => rfl
    | true =>
    exfalso
    have hx' : isHUD x = true := hxv
    have hr : IsSolZ ((t ++ s2) ++ [x]) := by
      have : IsSolZ ([x] ++ (t ++ s2)) := by rw [hsplit] at hc; simpa using hc
      exact isSolZ_rot this
    have hl : ((t ++ s2) ++ [x]).length = n := by rw [← hcn, hsplit]; simp; omega
    have h1 := hmax _ hr hl
    have h2 : s2.length + 1 ≤ tH isHUD ((t ++ s2) ++ [x]) := by
      rw [tH_snoc, if_pos hx']
      have := tH_all_suffix isHUD t s2 hs2
      omega
    omega
  · obtain ⟨i, l, hil⟩ : ∃ i l, s1 = i ++ [l] := by
      cases h : s1.reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.1 h) hne
      | cons l t => exact ⟨t.reverse, l, by rw [← List.reverse_reverse s1, h]; simp⟩
    refine ⟨i, l, hil, ?_⟩
    cases hlv : isHUD l with
    | false => rfl
    | true =>
    exfalso
    have hl : isHUD l = true := hlv
    have : s2.length + 1 ≤ tH isHUD c := by
      have := tH_all_suffix isHUD i (l :: s2) (by
        intro m hm; simp only [List.mem_cons] at hm; rcases hm with rfl | hm; exact hl; exact hs2 m hm)
      rw [hsplit, hil]; simpa using this
    omega
  · intro u v a b e hf
    have hc' : IsSolZ (u ++ a :: b :: (v ++ s2)) := by rw [hsplit, e] at hc; simpa using hc
    obtain ⟨w, hw, hwl⟩ := isSolZ_merge hc' hf
    have := hmin w hw
    have hl2 : (u ++ a :: b :: (v ++ s2)).length = n := by rw [← hcn, hsplit, e]; simp
    omega
  · intro p p' hp a ha
    have hrot : IsSolZ ((p' ++ s2) ++ p) := by
      have : IsSolZ (p ++ (p' ++ s2)) := by rw [hsplit, hp] at hc; simpa using hc
      exact isSolZ_rot this
    have hl : ((p' ++ s2) ++ p).length = n := by rw [← hcn, hsplit, hp]; simp; omega
    have hS := norm_parts.1
    have hmem : muSArr ∈ [muSArr, muYArr, muYiArr, muZArr] := by simp
    have hbig := hmax _ hrot hl
    rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl
    · show tH isHUD p ≤ s2.length
      have := tH_suffix isHUD (p' ++ s2) p
      omega
    · show tH (fun m => isHUD (muS m)) p ≤ s2.length
      rw [tH_map]
      have h1 := hmax _ (isSolZ_map (μa := muSArr) hS hmem hrot) (by simp only [List.length_map]; exact hl)
      have h2 := tH_suffix isHUD ((p' ++ s2).map muS) (p.map muS)
      rw [← List.map_append] at h2
      have e : (fun m => muSArr[m]!) = muS := rfl
      rw [e] at h1
      omega
    · show tH (fun m => isHUD (muS (muS m))) p ≤ s2.length
      have e : tH (fun m => isHUD (muS (muS m))) p = tH isHUD ((p.map muS).map muS) := by
        rw [← tH_map, ← tH_map]
      rw [e]
      have e2 : (fun m => muSArr[m]!) = muS := rfl
      have h0 := isSolZ_map (μa := muSArr) hS hmem hrot
      rw [e2] at h0
      have h1' := isSolZ_map (μa := muSArr) hS hmem h0
      rw [e2] at h1'
      have h1 := hmax _ h1' (by simp only [List.length_map]; exact hl)
      have h2 := tH_suffix isHUD (((p' ++ s2).map muS).map muS) ((p.map muS).map muS)
      rw [← List.map_append, ← List.map_append] at h2
      omega

-- ---------- the normal form ----------
/-- a maximal word can be rotated so that it starts with R or R' -/
theorem first_RR {n : Nat} (hmin : ∀ w, IsSolZ w → n ≤ w.length) {c : List Nat} (hc : IsSolZ c) (hcn : c.length = n)
    (hmax : ∀ w, IsSolZ w → w.length = n → tH isHUD w ≤ tH isHUD c) :
    ∃ c1, IsSolZ c1 ∧ c1.length = n ∧ tH isHUD c1 = tH isHUD c ∧ ∃ t, (c1 = 3 :: t ∨ c1 = 5 :: t) := by
  let L := c.reverse
  let r := tH isHUD c
  have hsp := tRev_split isHUD L
  let s2 := (L.take r).reverse
  let s1 := (L.drop r).reverse
  have hsplit : c = s1 ++ s2 := by
    show c = (L.drop r).reverse ++ (L.take r).reverse
    rw [← List.reverse_append, List.take_append_drop, List.reverse_reverse]
  have hs2 : ∀ m ∈ s2, isHUD m = true := fun m hm => hsp.1 m (List.mem_reverse.1 hm)
  have hrL : r ≤ L.length := by have := tH_le isHUD c; simp [L]; omega
  have hlen : s2.length = r := by simp [s2]; omega
  obtain ⟨⟨x, t, hxt, hx⟩, -, -, -⟩ := max_propsZ hmin hc hcn hmax hsplit hs2 hlen
  have hx18 : x < 18 := hc.1.1 x (by rw [hsplit, hxt]; simp)
  obtain ⟨-, -, -, hfirst⟩ := move_map_facts hx18
  have hcx : c = x :: (t ++ s2) := by rw [hsplit, hxt]; simp
  have gen : ∀ (μa : Array Nat) (T Ti : St), RotOK T Ti (fun m => μa[m]!) →
      μa ∈ [muSArr, muYArr, muYiArr, muZArr] → (∀ m < 18, isHUD μa[m]! = isHUD m) → (μa[x]! = 3 ∨ μa[x]! = 5) →
      ∃ c1, IsSolZ c1 ∧ c1.length = n ∧ tH isHUD c1 = tH isHUD c ∧ ∃ t, (c1 = 3 :: t ∨ c1 = 5 :: t) := by
    intro μa T Ti hT hmem hH hμx
    refine ⟨c.map (fun m => μa[m]!), isSolZ_map hT hmem hc, by simp [hcn], ?_, ?_⟩
    · rw [← tH_map]; unfold tH
      have : ∀ L : List Nat, (∀ m ∈ L, m < 18) → tRev (fun m => isHUD μa[m]!) L = tRev isHUD L := by
        intro L hL
        induction L with
        | nil => rfl
        | cons m t ih =>
          have e1 := hH m (hL m (by simp))
          have e2 := ih (fun k hk => hL k (by simp [hk]))
          simp only [tRev, e1, e2]
      exact this _ (fun m hm => hc.1.1 m (List.mem_reverse.1 hm))
    · refine ⟨(t ++ s2).map (fun m => μa[m]!), ?_⟩
      rw [hcx]
      rcases hμx with h | h
      · left; simp [h]
      · right; simp [h]
  have hRot := norm_parts
  rcases hfirst hx with h0 | h1 | h2 | h3
  · refine ⟨c, hc, hcn, rfl, t ++ s2, ?_⟩
    rcases h0 with h | h
    · left; rw [hcx, h]
    · right; rw [hcx, h]
  · exact gen muYArr Yst Yist hRot.2.1 (by simp) (fun m hm => (move_map_facts hm).1) h1
  · exact gen muYiArr Yist Yst hRot.2.2.1 (by simp) (fun m hm => (move_map_facts hm).2.1) h2
  · exact gen muZArr Z2st Z2st hRot.2.2.2 (by simp) (fun m hm => (move_map_facts hm).2.2.1) h3

/-- **Normal form on the supercube.** A solution of the superflip with all centres at home and at most 21 moves can
be brought into the form `s1 ++ s2` of `SfNorm`, with commuting moves on opposite faces in increasing face order
inside `s1` and inside `s2`. -/
theorem normal_formZ (w0 : List Nat) (hw0 : IsSolZ w0) (hl0 : w0.length ≤ 21) :
    ∃ s1 s2 : List Nat, IsSolZ (s1 ++ s2) ∧ (s1 ++ s2).length ≤ 21 ∧ (∀ m ∈ s2, isHUD m = true) ∧
      (∃ x t, s1 = x :: t ∧ (x = 3 ∨ x = 5)) ∧ (∃ i l, s1 = i ++ [l] ∧ isHUD l = false) ∧ NoAdj s1 ∧
      NoAdj (s1 ++ s2) ∧ Canon s1 ∧ Canon s2 ∧ (runOf s1).mx ≤ s2.length := by
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
  obtain ⟨c1, hc1, hc1n, hc1t, hc1h⟩ := first_RR hmin hc hcn hmax
  -- a word of least key among the maximal words starting with R or R'
  obtain ⟨kk, ⟨c2, hc2, hc2n, hc2t, hc2h, hc2k⟩, hkk⟩ :=
    exists_least (P := fun k => ∃ w, IsSolZ w ∧ w.length = n ∧ tH isHUD w = tH isHUD c ∧
        (∃ t, (w = 3 :: t ∨ w = 5 :: t)) ∧ keyR w = k) _ _ (Nat.le_refl _) ⟨c1, hc1, hc1n, hc1t, hc1h, rfl⟩
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
  have hrL : r ≤ L.length := by have := tH_le isHUD c2; simp [L]; omega
  have hlen : s2.length = r := by simp [s2]; omega
  obtain ⟨⟨x, t, hxt, hx⟩, hlast, hadj, hruns⟩ := max_propsZ hmin hc2 hc2n hmax2 hsplit hs2 hlen
  have hc2x : c2 = x :: (t ++ s2) := by rw [hsplit, hxt]; simp
  have hx35 : x = 3 ∨ x = 5 := by
    obtain ⟨t', h | h⟩ := hc2h
    · rw [hc2x] at h; simp only [List.cons.injEq] at h; left; exact h.1
    · rw [hc2x] at h; simp only [List.cons.injEq] at h; right; exact h.1
  -- swapping a descending pair keeps everything but lowers the key
  have noswap : ∀ c3 : List Nat, IsSolZ c3 → c3.length = n → s2.length ≤ tH isHUD c3 →
      (∃ t, (c3 = 3 :: t ∨ c3 = 5 :: t)) → keyR c3 < keyR c2 → False := by
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
  refine ⟨s1, s2, by rw [← hsplit]; exact hc2, by rw [← hsplit, hc2n]; exact hn, hs2, ⟨x, t, hxt, hx35⟩, hlast,
    hadj, by rw [← hsplit]; exact hadjAll, ?_, ?_, runOf_mx_le _ _ hruns⟩
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
        rw [← e.1] at hlt hax
        rcases hx35 with rfl | rfl <;> omega
      | cons y u' =>
        obtain ⟨t', h | h⟩ := hc2h
        · refine ⟨u' ++ b :: a :: (v ++ s2), Or.inl ?_⟩
          rw [hc2e] at h; simp only [List.cons_append, List.cons.injEq] at h; simp [h.1]
        · refine ⟨u' ++ b :: a :: (v ++ s2), Or.inr ?_⟩
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
    · obtain ⟨t', h | h⟩ := hc2h
      · refine ⟨t ++ u ++ b :: a :: v, Or.inl ?_⟩
        rw [hc2x] at h; simp only [List.cons.injEq] at h; rw [hxt, h.1]; simp
      · refine ⟨t ++ u ++ b :: a :: v, Or.inr ?_⟩
        rw [hc2x] at h; simp only [List.cons.injEq] at h; rw [hxt, h.1]; simp
    · rw [hc2e]; exact keyR_swap (s1 ++ u) v hlt
