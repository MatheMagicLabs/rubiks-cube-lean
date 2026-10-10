import CubeP.SfAlg
open Std

/-! Normal form of a shortest superflip solution: rotate it cyclically and conjugate it by whole-cube rotations so
that it ends with a longest run of ⟨U,D,R2,L2,F2,B2⟩-moves and starts with R or R'. -/

-- ---------- whole-cube rotations ----------
/-- 120° rotation about the URF–DBL diagonal (axis change U → R → F) -/
def Sst : St := ⟨#[0,4,5,1,3,7,6,2], #[1,2,1,2,2,1,2,1], #[1,8,5,9,3,11,7,10,0,4,6,2], #[1,0,1,0,1,0,1,0,1,1,1,1]⟩
def Sist : St := ⟨#[0,3,7,4,1,2,6,5], #[2,1,2,1,1,2,1,2], #[8,0,11,4,9,2,10,6,1,3,7,5], #[1,1,1,1,1,1,1,1,0,0,0,0]⟩
/-- quarter rotation about the U–D axis -/
def Yst : St := ⟨#[3,0,1,2,7,4,5,6], #[0,0,0,0,0,0,0,0], #[3,0,1,2,7,4,5,6,11,8,9,10], #[0,0,0,0,0,0,0,0,1,1,1,1]⟩
def Yist : St := ⟨#[1,2,3,0,5,6,7,4], #[0,0,0,0,0,0,0,0], #[1,2,3,0,5,6,7,4,9,10,11,8], #[0,0,0,0,0,0,0,0,1,1,1,1]⟩
/-- half rotation about the F–B axis -/
def Z2st : St := ⟨#[5,4,7,6,1,0,3,2], #[0,0,0,0,0,0,0,0], #[6,5,4,7,2,1,0,3,9,8,11,10], #[0,0,0,0,0,0,0,0,0,0,0,0]⟩
def muYArr : Array Nat := #[0,1,2,15,16,17,3,4,5,9,10,11,6,7,8,12,13,14]
def muYiArr : Array Nat := #[0,1,2,6,7,8,12,13,14,9,10,11,15,16,17,3,4,5]
def muZArr : Array Nat := #[9,10,11,12,13,14,6,7,8,0,1,2,3,4,5,15,16,17]

def rotB (T Ti : St) (μa : Array Nat) : Bool :=
  validB T && validB Ti && T.mul Ti == St.id && Ti.mul T == St.id &&
  (List.range 18).all (fun m => decide (μa[m]! < 18) && (T.mul moves[m]!).mul Ti == moves[μa[m]!]!) &&
  (T.mul sfSt).mul Ti == sfSt

/-- facts about move maps: the U–D rotations keep ⟨U,D,R2,L2,F2,B2⟩; every move outside it is sent to R or R' by
one of them; consecutive moves on one face merge -/
def mergeOf (a b : Nat) : Nat := 3 * (a / 3) + ((a % 3 + b % 3 + 1) % 4)
def normFactsB : Bool :=
  rotB Sst Sist muSArr && rotB Yst Yist muYArr && rotB Yist Yst muYiArr && rotB Z2st Z2st muZArr &&
  (List.range 18).all (fun m =>
    isHUD muYArr[m]! == isHUD m && isHUD muYiArr[m]! == isHUD m && isHUD muZArr[m]! == isHUD m &&
    (isHUD m || m == 3 || m == 5 || muYArr[m]! == 3 || muYArr[m]! == 5 || muYiArr[m]! == 3 || muYiArr[m]! == 5 ||
      muZArr[m]! == 3 || muZArr[m]! == 5)) &&
  (List.range 18).all (fun a => (List.range 18).all (fun b => a / 3 != b / 3 ||
    (if (a % 3 + b % 3 + 1) % 4 == 3 then (moves[a]!).mul moves[b]! == St.id
     else decide (mergeOf a b < 18) && (moves[a]!).mul moves[b]! == moves[mergeOf a b]!)))
theorem normFacts_true : normFactsB = true := by native_decide

theorem rotOK_of {T Ti : St} {μa : Array Nat} (h : rotB T Ti μa = true) : RotOK T Ti (fun m => μa[m]!) := by
  unfold rotB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨valid_of_B h1, valid_of_B h2, h3, h4, fun m hm => ?_, h6⟩
  have := lt_of_range_all h5 hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this

theorem norm_parts : RotOK Sst Sist muS ∧ RotOK Yst Yist (fun m => muYArr[m]!) ∧
    RotOK Yist Yst (fun m => muYiArr[m]!) ∧ RotOK Z2st Z2st (fun m => muZArr[m]!) := by
  have h := normFacts_true; unfold normFactsB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨rotOK_of h.1.1.1.1.1, rotOK_of h.1.1.1.1.2, rotOK_of h.1.1.1.2, rotOK_of h.1.1.2⟩

theorem move_map_facts {m : Nat} (hm : m < 18) :
    isHUD muYArr[m]! = isHUD m ∧ isHUD muYiArr[m]! = isHUD m ∧ isHUD muZArr[m]! = isHUD m ∧
    (isHUD m = false → (m = 3 ∨ m = 5) ∨ (muYArr[m]! = 3 ∨ muYArr[m]! = 5) ∨ (muYiArr[m]! = 3 ∨ muYiArr[m]! = 5) ∨
      (muZArr[m]! = 3 ∨ muZArr[m]! = 5)) := by
  have h := normFacts_true; unfold normFactsB at h
  simp only [Bool.and_eq_true] at h
  have := lt_of_range_all h.1.2 hm
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at this
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := this
  refine ⟨e1, e2, e3, fun hn => ?_⟩
  rw [hn] at e4
  simp only [Bool.false_eq_true, false_or] at e4
  omega

theorem merge_fact {a b : Nat} (ha : a < 18) (hb : b < 18) (hf : a / 3 = b / 3) :
    (moves[a]!).mul moves[b]! = St.id ∨ ∃ c, c < 18 ∧ (moves[a]!).mul moves[b]! = moves[c]! := by
  have h := normFacts_true; unfold normFactsB at h
  simp only [Bool.and_eq_true] at h
  have := lt_of_range_all (lt_of_range_all h.2 ha) hb
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  rcases this with h1 | h1
  · exact absurd hf h1
  · split at h1
    · left; exact of_decide_eq_true (by simpa using h1)
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      exact Or.inr ⟨_, h1.1, h1.2⟩

-- ---------- solutions ----------
def IsSol (w : List Nat) : Prop := (∀ m ∈ w, m < 18) ∧ eval w = sfSt

theorem isSol_rot {a b : List Nat} (h : IsSol (a ++ b)) : IsSol (b ++ a) := by
  have ha : ∀ k ∈ a, k < 18 := fun k hk => h.1 k (by simp [hk])
  have hb : ∀ k ∈ b, k < 18 := fun k hk => h.1 k (by simp [hk])
  exact ⟨all_append hb ha, sol_rot ha hb h.2⟩

theorem isSol_map {T Ti : St} {μ : Nat → Nat} (hT : RotOK T Ti μ) {w : List Nat} (h : IsSol w) : IsSol (w.map μ) :=
  ⟨map_lt (fun m hm => (hT.mv m hm).1) h.1, sol_cj hT h.1 h.2⟩

/-- two consecutive moves on one face can be merged: a strictly shorter solution exists -/
theorem isSol_merge {u v : List Nat} {a b : Nat} (h : IsSol (u ++ a :: b :: v)) (hf : a / 3 = b / 3) :
    ∃ w, IsSol w ∧ w.length < (u ++ a :: b :: v).length := by
  have hu : ∀ k ∈ u, k < 18 := fun k hk => h.1 k (by simp [hk])
  have hv : ∀ k ∈ v, k < 18 := fun k hk => h.1 k (by simp [hk])
  have ha : a < 18 := h.1 a (by simp)
  have hb : b < 18 := h.1 b (by simp)
  have hab : ∀ k ∈ [a, b], k < 18 := by simp [ha, hb]
  have e : eval (u ++ a :: b :: v) = ((eval u).mul ((moves[a]!).mul moves[b]!)).mul (eval v) := by
    have e1 : u ++ a :: b :: v = (u ++ [a, b]) ++ v := by simp
    rw [e1, eval_app hv (all_append hu hab), eval_app hab hu, eval_cons ha (by simp [hb]),
      eval_cons hb (by simp), show eval ([] : List Nat) = St.id from rfl, mul_id (move_facts hb).1]
  rcases merge_fact ha hb hf with h1 | ⟨c, hc, h1⟩
  · refine ⟨u ++ v, ⟨all_append hu hv, ?_⟩, by simp; omega⟩
    rw [eval_app hv hu, ← h.2, e, h1, mul_id (valid_eval u hu)]
  · refine ⟨u ++ c :: v, ⟨all_append hu (by intro k hk; simp at hk; rcases hk with rfl | hk; exact hc; exact hv k hk), ?_⟩,
      by simp⟩
    have hcv : ∀ k ∈ c :: v, k < 18 := by intro k hk; simp at hk; rcases hk with rfl | hk; exact hc; exact hv k hk
    rw [eval_app hcv hu, eval_cons hc hv, ← h.2, e, h1, mul_assoc' _ (move_facts hc).1 (valid_eval v hv)]

def NoAdj (w : List Nat) : Prop := ∀ u v a b, w = u ++ a :: b :: v → a / 3 ≠ b / 3

-- ---------- trailing runs ----------
def tRev (h : Nat → Bool) : List Nat → Nat
  | [] => 0
  | m :: t => if h m then tRev h t + 1 else 0

/-- length of the longest suffix of `w` all of whose moves satisfy `h` -/
def tH (h : Nat → Bool) (w : List Nat) : Nat := tRev h w.reverse

theorem tRev_le (h : Nat → Bool) : ∀ L : List Nat, tRev h L ≤ L.length
  | [] => by simp [tRev]
  | m :: t => by
    unfold tRev; split
    · have := tRev_le h t; simp; omega
    · simp

theorem tRev_app (h : Nat → Bool) : ∀ L M : List Nat, tRev h L ≤ tRev h (L ++ M)
  | [], _ => by simp [tRev]
  | m :: t, M => by
    show tRev h (m :: t) ≤ tRev h (m :: (t ++ M))
    unfold tRev; split
    · have := tRev_app h t M; omega
    · omega

theorem tRev_all (h : Nat → Bool) : ∀ L M : List Nat, (∀ m ∈ L, h m = true) → L.length ≤ tRev h (L ++ M)
  | [], _, _ => by simp
  | m :: t, M, hL => by
    show (m :: t).length ≤ tRev h (m :: (t ++ M))
    unfold tRev
    rw [if_pos (hL m (by simp))]
    have := tRev_all h t M (fun k hk => hL k (by simp [hk]))
    simp; omega

theorem tRev_map (h : Nat → Bool) (μ : Nat → Nat) : ∀ L : List Nat, tRev (fun m => h (μ m)) L = tRev h (L.map μ)
  | [] => rfl
  | m :: t => by
    simp only [tRev, List.map_cons]
    rw [tRev_map h μ t]

theorem tH_snoc (h : Nat → Bool) (w : List Nat) (m : Nat) :
    tH h (w ++ [m]) = if h m then tH h w + 1 else 0 := by
  unfold tH; rw [List.reverse_append]; rfl

theorem tH_suffix (h : Nat → Bool) (x y : List Nat) : tH h y ≤ tH h (x ++ y) := by
  unfold tH; rw [List.reverse_append]; exact tRev_app h _ _

theorem tH_le (h : Nat → Bool) (w : List Nat) : tH h w ≤ w.length := by
  have := tRev_le h w.reverse; unfold tH; simpa using this

theorem tH_map (h : Nat → Bool) (μ : Nat → Nat) (w : List Nat) : tH (fun m => h (μ m)) w = tH h (w.map μ) := by
  unfold tH; rw [tRev_map, List.map_reverse]

/-- a run of `h`-moves at the end of a word -/
theorem tH_all_suffix (h : Nat → Bool) (x s : List Nat) (hs : ∀ m ∈ s, h m = true) : s.length ≤ tH h (x ++ s) := by
  unfold tH; rw [List.reverse_append]
  have := tRev_all h s.reverse x.reverse (fun m hm => hs m (List.mem_reverse.1 hm))
  simpa using this

/-- splitting off the trailing run -/
theorem tRev_split (h : Nat → Bool) : ∀ L : List Nat,
    (∀ m ∈ L.take (tRev h L), h m = true) ∧ (∀ x t, L.drop (tRev h L) = x :: t → h x = false)
  | [] => by simp [tRev]
  | m :: t => by
    by_cases hm : h m = true
    · have ih := tRev_split h t
      have e : tRev h (m :: t) = tRev h t + 1 := by simp [tRev, hm]
      rw [e]
      refine ⟨fun k hk => ?_, fun x t' hx => ih.2 x t' (by simpa using hx)⟩
      simp only [List.take_succ_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact hm
      · exact ih.1 k hk
    · have e : tRev h (m :: t) = 0 := by simp [tRev, hm]
      rw [e]
      refine ⟨by simp, fun x t' hx => ?_⟩
      simp only [List.drop_zero, List.cons.injEq] at hx
      rw [← hx.1]; simpa using hm

-- ---------- runs and the search state ----------
theorem snoc_ind {motive : List Nat → Prop} (nil : motive []) (append_singleton : ∀ w m, motive w → motive (w ++ [m])) :
    ∀ w, motive w := by
  intro w
  rw [← List.reverse_reverse w]
  generalize w.reverse = l
  induction l with
  | nil => exact nil
  | cons m t ih => rw [List.reverse_cons]; exact append_singleton _ _ ih

theorem runOf_snoc (w : List Nat) (m : Nat) : runOf (w ++ [m]) = runStep (runOf w) m := by
  unfold runOf; rw [List.foldl_append]; rfl

theorem runStep_r0 (s : RunSt) (m : Nat) : (runStep s m).r0 = if isHa 0 m then s.r0 + 1 else 0 := rfl
theorem runStep_r1 (s : RunSt) (m : Nat) : (runStep s m).r1 = if isHa 1 m then s.r1 + 1 else 0 := rfl
theorem runStep_r2 (s : RunSt) (m : Nat) : (runStep s m).r2 = if isHa 2 m then s.r2 + 1 else 0 := rfl
theorem runStep_mx (s : RunSt) (m : Nat) :
    (runStep s m).mx = max s.mx (max (runStep s m).r0 (max (runStep s m).r1 (runStep s m).r2)) := rfl

theorem runOf_runs (w : List Nat) :
    (runOf w).r0 = tH (isHa 0) w ∧ (runOf w).r1 = tH (isHa 1) w ∧ (runOf w).r2 = tH (isHa 2) w := by
  induction w using snoc_ind with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | append_singleton w m ih =>
    obtain ⟨e0, e1, e2⟩ := ih
    rw [runOf_snoc, tH_snoc, tH_snoc, tH_snoc, runStep_r0, runStep_r1, runStep_r2, e0, e1, e2]
    exact ⟨rfl, rfl, rfl⟩

theorem runOf_mx_le (R : Nat) : ∀ w : List Nat,
    (∀ p p' : List Nat, w = p ++ p' → ∀ a < 3, tH (isHa a) p ≤ R) → (runOf w).mx ≤ R := by
  intro w
  induction w using snoc_ind with
  | nil => intro _; show 0 ≤ R; exact Nat.zero_le _
  | append_singleton w m ih =>
    intro hw
    have h1 := ih (fun p p' e a ha => hw p (p' ++ [m]) (by rw [e]; simp) a ha)
    have h2 : ∀ a < 3, tH (isHa a) (w ++ [m]) ≤ R := fun a ha => hw (w ++ [m]) [] (by simp) a ha
    obtain ⟨e0, e1, e2⟩ := runOf_runs (w ++ [m])
    have a0 := h2 0 (by decide); have a1 := h2 1 (by decide); have a2 := h2 2 (by decide)
    rw [← e0] at a0; rw [← e1] at a1; rw [← e2] at a2
    rw [runOf_snoc] at a0 a1 a2 ⊢
    rw [runStep_mx]
    exact Nat.max_le.2 ⟨h1, Nat.max_le.2 ⟨a0, Nat.max_le.2 ⟨a1, a2⟩⟩⟩

theorem runOf_mx_mono (w : List Nat) : ∀ v : List Nat, (runOf w).mx ≤ (runOf (w ++ v)).mx := by
  intro v
  induction v using snoc_ind with
  | nil => simp
  | append_singleton v m ih =>
    rw [← List.append_assoc, runOf_snoc, runStep_mx]
    exact Nat.le_trans ih (Nat.le_max_left _ _)

-- ---------- the normal form ----------
theorem exists_least {P : Nat → Prop} : ∀ N n, n ≤ N → P n → ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  intro N
  induction N with
  | zero =>
    intro n hn hp
    have : n = 0 := by omega
    subst this; exact ⟨0, hp, fun k _ => Nat.zero_le _⟩
  | succ N ih =>
    intro n hn hp
    rcases Classical.em (∃ k, k < n ∧ P k) with ⟨k, hk, hpk⟩ | hno
    · exact ih k (by omega) hpk
    · refine ⟨n, hp, fun k hk => ?_⟩
      rcases Nat.lt_or_ge k n with h | h
      · exact absurd ⟨k, h, hk⟩ hno
      · exact h

theorem eo_of_H (s : List Nat) (hs : ∀ m ∈ s, isHUD m = true) : (eval s).eo = eoZero := by
  have hg : ∀ m ∈ s, m ∈ g2Moves := fun m hm => List.contains_iff_mem.1 (hs m hm)
  exact (g2_keep s hg St.id rfl rfl rfl).1

theorem sf_eo_ne : sfSt.eo ≠ eoZero := by decide

/-- properties of a solution that is shortest and has a longest trailing H-run -/
theorem max_props {n : Nat} (hmin : ∀ w, IsSol w → n ≤ w.length) {c : List Nat} (hc : IsSol c) (hcn : c.length = n)
    (hmax : ∀ w, IsSol w → w.length = n → tH isHUD w ≤ tH isHUD c) {s1 s2 : List Nat} (hsplit : c = s1 ++ s2)
    (hs2 : ∀ m ∈ s2, isHUD m = true) (hlen : s2.length = tH isHUD c) :
    (∃ x t, s1 = x :: t ∧ isHUD x = false) ∧ (∃ i l, s1 = i ++ [l] ∧ isHUD l = false) ∧ NoAdj s1 ∧
      (∀ p p' : List Nat, s1 = p ++ p' → ∀ a < 3, tH (isHa a) p ≤ s2.length) := by
  -- s1 is not empty
  have hne : s1 ≠ [] := by
    intro h0
    rw [h0, List.nil_append] at hsplit
    have := eo_of_H s2 hs2
    rw [← hsplit, hc.2] at this
    exact sf_eo_ne this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the first move is outside H
    obtain ⟨x, t, rfl⟩ : ∃ x t, s1 = x :: t := by
      cases s1 with
      | nil => exact absurd rfl hne
      | cons x t => exact ⟨x, t, rfl⟩
    refine ⟨x, t, rfl, ?_⟩
    cases hxv : isHUD x with
    | false => rfl
    | true =>
    exfalso
    have hx' : isHUD x = true := hxv
    have hr : IsSol ((t ++ s2) ++ [x]) := by
      have : IsSol ([x] ++ (t ++ s2)) := by rw [hsplit] at hc; simpa using hc
      exact isSol_rot this
    have hl : ((t ++ s2) ++ [x]).length = n := by rw [← hcn, hsplit]; simp; omega
    have h1 := hmax _ hr hl
    have h2 : s2.length + 1 ≤ tH isHUD ((t ++ s2) ++ [x]) := by
      rw [tH_snoc, if_pos hx']
      have := tH_all_suffix isHUD t s2 hs2
      omega
    omega
  · -- the last move of s1 is outside H
    obtain ⟨i, l, hil⟩ : ∃ i l, s1 = i ++ [l] := by
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
  · -- no two consecutive moves on one face
    intro u v a b e hf
    have hc' : IsSol (u ++ a :: b :: (v ++ s2)) := by rw [hsplit, e] at hc; simpa using hc
    obtain ⟨w, hw, hwl⟩ := isSol_merge hc' hf
    have := hmin w hw
    have hl2 : (u ++ a :: b :: (v ++ s2)).length = n := by rw [← hcn, hsplit, e]; simp
    omega
  · -- every run inside s1 is at most as long as s2
    intro p p' hp a ha
    have hrot : IsSol ((p' ++ s2) ++ p) := by
      have : IsSol (p ++ (p' ++ s2)) := by rw [hsplit, hp] at hc; simpa using hc
      exact isSol_rot this
    have hl : ((p' ++ s2) ++ p).length = n := by rw [← hcn, hsplit, hp]; simp; omega
    have hS := norm_parts.1
    have hbig := hmax _ hrot hl
    rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl
    · show tH isHUD p ≤ s2.length
      have := tH_suffix isHUD (p' ++ s2) p
      omega
    · show tH (fun m => isHUD (muS m)) p ≤ s2.length
      rw [tH_map]
      have h1 := hmax _ (isSol_map hS hrot) (by simp only [List.length_map]; exact hl)
      have h2 := tH_suffix isHUD ((p' ++ s2).map muS) (p.map muS)
      rw [← List.map_append] at h2
      omega
    · show tH (fun m => isHUD (muS (muS m))) p ≤ s2.length
      have e : tH (fun m => isHUD (muS (muS m))) p = tH isHUD ((p.map muS).map muS) := by
        rw [← tH_map, ← tH_map]
      rw [e]
      have h1 := hmax _ (isSol_map hS (isSol_map hS hrot)) (by simp only [List.length_map]; exact hl)
      have h2 := tH_suffix isHUD (((p' ++ s2).map muS).map muS) ((p.map muS).map muS)
      rw [← List.map_append, ← List.map_append] at h2
      omega

/-- **Normal form.** If the superflip has a solution of at most 19 moves, it has one of the form `s1 ++ s2` where
`s2` is a word of ⟨U,D,R2,L2,F2,B2⟩, `s1` starts with R or R', ends with a move outside that group, has no two
consecutive moves on one face, and contains no run of moves of any axis' phase-2 group longer than `s2`. -/
theorem normal_form (w0 : List Nat) (hw0 : IsSol w0) (hl0 : w0.length ≤ 19) :
    ∃ s1 s2 : List Nat, IsSol (s1 ++ s2) ∧ (s1 ++ s2).length ≤ 19 ∧ (∀ m ∈ s2, isHUD m = true) ∧
      (∃ x t, s1 = x :: t ∧ (x = 3 ∨ x = 5)) ∧ (∃ i l, s1 = i ++ [l] ∧ isHUD l = false) ∧ NoAdj s1 ∧
      (runOf s1).mx ≤ s2.length := by
  -- shortest solution length
  obtain ⟨n, ⟨w1, hw1, hw1l⟩, hminP⟩ := exists_least (P := fun n => ∃ w, IsSol w ∧ w.length = n) _ _
    (Nat.le_refl _) ⟨w0, hw0, rfl⟩
  have hmin : ∀ w, IsSol w → n ≤ w.length := fun w hw => hminP _ ⟨w, hw, rfl⟩
  have hn19 : n ≤ 19 := Nat.le_trans (hmin w0 hw0) hl0
  -- a shortest solution with the longest trailing H-run
  obtain ⟨k0, ⟨c, hc, hcn, hck⟩, hk0⟩ :=
    exists_least (P := fun k => ∃ w, IsSol w ∧ w.length = n ∧ tH isHUD w + k = n) _ _ (Nat.le_refl _)
      ⟨w1, hw1, hw1l, (by have := tH_le isHUD w1; omega : tH isHUD w1 + (n - tH isHUD w1) = n)⟩
  have hmax : ∀ w, IsSol w → w.length = n → tH isHUD w ≤ tH isHUD c := by
    intro w hw hwl
    rcases Nat.lt_or_ge (tH isHUD c) (tH isHUD w) with hlt | hge
    · exfalso
      have := hk0 (n - tH isHUD w) ⟨w, hw, hwl, (by have := tH_le isHUD w; omega)⟩
      have h2 := tH_le isHUD w
      omega
    · exact hge
  -- split off the trailing run
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
  obtain ⟨⟨x, t, hxt, hx⟩, -, -, -⟩ := max_props hmin hc hcn hmax hsplit hs2 hlen
  -- conjugate by a U–D rotation so that the first move becomes R or R'
  have hx18 : x < 18 := hc.1 x (by rw [hsplit, hxt]; simp)
  obtain ⟨-, -, -, hfirst⟩ := move_map_facts hx18
  have gen : ∀ (μ : Nat → Nat) (T Ti : St), RotOK T Ti μ → (∀ m < 18, isHUD (μ m) = isHUD m) → (μ x = 3 ∨ μ x = 5) →
      ∃ s1 s2 : List Nat, IsSol (s1 ++ s2) ∧ (s1 ++ s2).length ≤ 19 ∧ (∀ m ∈ s2, isHUD m = true) ∧
        (∃ x t, s1 = x :: t ∧ (x = 3 ∨ x = 5)) ∧ (∃ i l, s1 = i ++ [l] ∧ isHUD l = false) ∧ NoAdj s1 ∧
        (runOf s1).mx ≤ s2.length := by
    intro μ T Ti hT hH hμx
    have hc' : IsSol (c.map μ) := isSol_map hT hc
    have hcn' : (c.map μ).length = n := by simp [hcn]
    have htm : tH isHUD (c.map μ) = tH isHUD c := by
      rw [← tH_map]; unfold tH
      have : ∀ L : List Nat, (∀ m ∈ L, m < 18) → tRev (fun m => isHUD (μ m)) L = tRev isHUD L := by
        intro L hL
        induction L with
        | nil => rfl
        | cons m t ih =>
          have e1 := hH m (hL m (by simp))
          have e2 := ih (fun k hk => hL k (by simp [hk]))
          simp only [tRev, e1, e2]
      exact this _ (fun m hm => hc.1 m (List.mem_reverse.1 hm))
    have hmax' : ∀ w, IsSol w → w.length = n → tH isHUD w ≤ tH isHUD (c.map μ) := by
      intro w hw hwl; rw [htm]; exact hmax w hw hwl
    have hsplit' : c.map μ = s1.map μ ++ s2.map μ := by rw [hsplit, List.map_append]
    have hs2' : ∀ m ∈ s2.map μ, isHUD m = true := by
      intro m hm
      simp only [List.mem_map] at hm
      obtain ⟨a, ha, rfl⟩ := hm
      rw [hH a (hc.1 a (by rw [hsplit]; simp [ha]))]; exact hs2 a ha
    have hlen' : (s2.map μ).length = tH isHUD (c.map μ) := by rw [htm, List.length_map, hlen]
    obtain ⟨-, hlast, hadj, hruns⟩ := max_props hmin hc' hcn' hmax' hsplit' hs2' hlen'
    refine ⟨s1.map μ, s2.map μ, by rw [← hsplit']; exact hc', by rw [← hsplit', hcn']; exact hn19, hs2',
      ⟨μ x, t.map μ, by rw [hxt]; rfl, hμx⟩, hlast, hadj, ?_⟩
    exact runOf_mx_le _ _ hruns
  have hRot := norm_parts
  rcases hfirst hx with h0 | h1 | h2 | h3
  · exact gen id St.id St.id ⟨valid_id, valid_id, mul_id valid_id, mul_id valid_id,
      fun m hm => ⟨hm, by unfold id; rw [id_mul (move_facts hm).1, mul_id (move_facts hm).1]⟩,
      by rw [id_mul sfValid, mul_id sfValid]⟩ (fun m _ => rfl) h0
  · exact gen (fun m => muYArr[m]!) Yst Yist hRot.2.1 (fun m hm => (move_map_facts hm).1) h1
  · exact gen (fun m => muYiArr[m]!) Yist Yst hRot.2.2.1 (fun m hm => (move_map_facts hm).2.1) h2
  · exact gen (fun m => muZArr[m]!) Z2st Z2st hRot.2.2.2 (fun m hm => (move_map_facts hm).2.2.1) h3
