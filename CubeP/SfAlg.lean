import CubeP.Low2Proof
import CubeO.Sf
import CubeP.K28Proof
import CubeP.LowerProof
open Std

/-! Algebra of cube states, as needed for the superflip lower bound: validity, associativity, identities,
inverse words, centrality of the superflip, and conjugation by whole-cube rotations. -/

/-- a well-formed cube state: arrays of the right sizes with entries in range -/
def Valid (x : St) : Prop :=
  x.cp.size = 8 ∧ x.co.size = 8 ∧ x.ep.size = 12 ∧ x.eo.size = 12 ∧
  (∀ i < 8, x.cp[i]! < 8) ∧ (∀ i < 8, x.co[i]! < 3) ∧ (∀ i < 12, x.ep[i]! < 12) ∧ (∀ i < 12, x.eo[i]! < 2)

def validB (x : St) : Bool :=
  x.cp.size == 8 && x.co.size == 8 && x.ep.size == 12 && x.eo.size == 12 &&
  (List.range 8).all (fun i => decide (x.cp[i]! < 8)) && (List.range 8).all (fun i => decide (x.co[i]! < 3)) &&
  (List.range 12).all (fun i => decide (x.ep[i]! < 12)) && (List.range 12).all (fun i => decide (x.eo[i]! < 2))

theorem valid_of_B {x : St} (h : validB x = true) : Valid x := by
  unfold validB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, fun i hi => of_decide_eq_true (lt_of_range_all h5 hi),
    fun i hi => of_decide_eq_true (lt_of_range_all h6 hi), fun i hi => of_decide_eq_true (lt_of_range_all h7 hi),
    fun i hi => of_decide_eq_true (lt_of_range_all h8 hi)⟩

theorem St.ext' {x y : St} (h1 : x.cp = y.cp) (h2 : x.co = y.co) (h3 : x.ep = y.ep) (h4 : x.eo = y.eo) : x = y := by
  cases x; cases y; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

theorem mul_cp (s m : St) : (s.mul m).cp = (List.range 8).toArray.map (fun i => s.cp[m.cp[i]!]!) := rfl
theorem mul_co (s m : St) : (s.mul m).co = (List.range 8).toArray.map (fun i => (s.co[m.cp[i]!]! + m.co[i]!) % 3) := rfl
theorem mul_ep (s m : St) : (s.mul m).ep = (List.range 12).toArray.map (fun i => s.ep[m.ep[i]!]!) := rfl
theorem mul_eo (s m : St) : (s.mul m).eo = (List.range 12).toArray.map (fun i => (s.eo[m.ep[i]!]! + m.eo[i]!) % 2) := rfl

theorem valid_mul {a b : St} (ha : Valid a) (hb : Valid b) : Valid (a.mul b) := by
  obtain ⟨-, -, -, -, a5, a6, a7, a8⟩ := ha
  obtain ⟨-, -, -, -, b5, b6, b7, b8⟩ := hb
  refine ⟨by simp [mul_cp], by simp [mul_co], by simp [mul_ep], by simp [mul_eo], ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [mul_cp, gmr hi]; exact a5 _ (b5 i hi)
  · intro i hi; rw [mul_co, gmr hi]; exact Nat.mod_lt _ (by decide)
  · intro i hi; rw [mul_ep, gmr hi]; exact a7 _ (b7 i hi)
  · intro i hi; rw [mul_eo, gmr hi]; exact Nat.mod_lt _ (by decide)

theorem mul_assoc' (a : St) {b c : St} (hb : Valid b) (hc : Valid c) : (a.mul b).mul c = a.mul (b.mul c) := by
  obtain ⟨-, -, -, -, b5, -, b7, -⟩ := hb
  obtain ⟨-, -, -, -, c5, -, c7, -⟩ := hc
  apply St.ext'
  · rw [mul_cp, mul_cp, mul_cp, mul_cp]
    apply map_range_congr; intro i hi; rw [gmr (c5 i hi), gmr hi]
  · rw [mul_co, mul_co, mul_co, mul_co, mul_cp]
    apply map_range_congr; intro i hi; rw [gmr (c5 i hi), gmr hi, gmr hi]; omega
  · rw [mul_ep, mul_ep, mul_ep, mul_ep]
    apply map_range_congr; intro i hi; rw [gmr (c7 i hi), gmr hi]
  · rw [mul_eo, mul_eo, mul_eo, mul_eo, mul_ep]
    apply map_range_congr; intro i hi; rw [gmr (c7 i hi), gmr hi, gmr hi]; omega

theorem idco : ∀ i < 8, St.id.co[i]! = 0 := by decide
theorem ideo : ∀ i < 12, St.id.eo[i]! = 0 := by decide

theorem valid_id : Valid St.id := valid_of_B (by decide)

theorem mul_id {x : St} (hx : Valid x) : x.mul St.id = x := by
  obtain ⟨s1, s2, s3, s4, -, x6, -, x8⟩ := hx
  apply St.ext'
  · rw [mul_cp]; refine (map_range_congr (g := fun i => x.cp[i]!) ?_).trans (map_range_self s1)
    intro i hi; rw [idc i hi]
  · rw [mul_co]; refine (map_range_congr (g := fun i => x.co[i]!) ?_).trans (map_range_self s2)
    intro i hi; rw [idc i hi, idco i hi, Nat.add_zero, Nat.mod_eq_of_lt (x6 i hi)]
  · rw [mul_ep]; refine (map_range_congr (g := fun i => x.ep[i]!) ?_).trans (map_range_self s3)
    intro i hi; rw [ide i hi]
  · rw [mul_eo]; refine (map_range_congr (g := fun i => x.eo[i]!) ?_).trans (map_range_self s4)
    intro i hi; rw [ide i hi, ideo i hi, Nat.add_zero, Nat.mod_eq_of_lt (x8 i hi)]

theorem id_mul {x : St} (hx : Valid x) : St.id.mul x = x := by
  obtain ⟨s1, s2, s3, s4, x5, x6, x7, x8⟩ := hx
  apply St.ext'
  · rw [mul_cp]; refine (map_range_congr (g := fun i => x.cp[i]!) ?_).trans (map_range_self s1)
    intro i hi; rw [idc _ (x5 i hi)]
  · rw [mul_co]; refine (map_range_congr (g := fun i => x.co[i]!) ?_).trans (map_range_self s2)
    intro i hi; rw [idco _ (x5 i hi), Nat.zero_add, Nat.mod_eq_of_lt (x6 i hi)]
  · rw [mul_ep]; refine (map_range_congr (g := fun i => x.ep[i]!) ?_).trans (map_range_self s3)
    intro i hi; rw [ide _ (x7 i hi)]
  · rw [mul_eo]; refine (map_range_congr (g := fun i => x.eo[i]!) ?_).trans (map_range_self s4)
    intro i hi; rw [ideo _ (x7 i hi), Nat.zero_add, Nat.mod_eq_of_lt (x8 i hi)]

-- ---------- moves and words ----------
def minv (m : Nat) : Nat := 3 * (m / 3) + (2 - m % 3)

def moveFactsB : Bool := (List.range 18).all (fun m =>
  validB moves[m]! && decide (minv m < 18) && (moves[m]!).mul moves[minv m]! == St.id && minv (minv m) == m &&
  (!g2Moves.contains m || g2Moves.contains (minv m)))
theorem moveFacts_true : moveFactsB = true := by native_decide

theorem move_facts {m : Nat} (hm : m < 18) : Valid moves[m]! ∧ minv m < 18 ∧ (moves[m]!).mul moves[minv m]! = St.id ∧
    minv (minv m) = m ∧ (m ∈ g2Moves → minv m ∈ g2Moves) := by
  have h := lt_of_range_all moveFacts_true hm
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨valid_of_B h1, h2, h3, h4, fun hg => ?_⟩
  rcases h5 with h5 | h5
  · have : g2Moves.contains m = true := List.contains_iff_mem.2 hg
    rw [this] at h5; exact absurd h5 (by simp)
  · exact h5

theorem apply_eq (x : St) (m : Nat) : apply x m = x.mul moves[m]! := rfl

theorem valid_applyList : ∀ (w : List Nat), (∀ m ∈ w, m < 18) → ∀ x, Valid x → Valid (applyList x w) := by
  intro w
  induction w with
  | nil => intro _ x hx; exact hx
  | cons m w ih =>
    intro hw x hx
    rw [applyList_cons']
    exact ih (fun k hk => hw k (by simp [hk])) _ (valid_mul hx (move_facts (hw m (by simp))).1)

theorem valid_eval (w : List Nat) (hw : ∀ m ∈ w, m < 18) : Valid (eval w) := valid_applyList w hw _ valid_id

theorem applyList_eq : ∀ (w : List Nat), (∀ m ∈ w, m < 18) → ∀ x, Valid x → applyList x w = x.mul (eval w) := by
  intro w
  induction w with
  | nil => intro _ x hx; exact (mul_id hx).symm
  | cons m w ih =>
    intro hw x hx
    have hm := move_facts (hw m (by simp))
    have hw' : ∀ k ∈ w, k < 18 := fun k hk => hw k (by simp [hk])
    have hE : eval (m :: w) = moves[m]!.mul (eval w) := by
      show applyList (apply St.id m) w = _
      rw [apply_eq, id_mul hm.1, ih hw' _ hm.1]
    rw [applyList_cons', apply_eq, ih hw' _ (valid_mul hx hm.1), hE, mul_assoc' _ hm.1 (valid_eval w hw')]

theorem eval_cons {m : Nat} (hm : m < 18) {w : List Nat} (hw : ∀ k ∈ w, k < 18) :
    eval (m :: w) = moves[m]!.mul (eval w) := by
  show applyList (apply St.id m) w = _
  rw [apply_eq, id_mul (move_facts hm).1, applyList_eq w hw _ (move_facts hm).1]

theorem eval_app {u v : List Nat} (hv : ∀ k ∈ v, k < 18) (hu : ∀ k ∈ u, k < 18) :
    eval (u ++ v) = (eval u).mul (eval v) := by
  rw [eval_append, applyList_eq v hv _ (valid_eval u hu)]

def winv (w : List Nat) : List Nat := (w.map minv).reverse

theorem winv_cons (m : Nat) (w : List Nat) : winv (m :: w) = winv w ++ [minv m] := by
  simp [winv]

theorem winv_lt {w : List Nat} (hw : ∀ k ∈ w, k < 18) : ∀ k ∈ winv w, k < 18 := by
  intro k hk
  simp only [winv, List.mem_reverse, List.mem_map] at hk
  obtain ⟨a, ha, rfl⟩ := hk
  exact (move_facts (hw a ha)).2.1

theorem winv_g2 {w : List Nat} (hw : ∀ k ∈ w, k ∈ g2Moves) : ∀ k ∈ winv w, k ∈ g2Moves := by
  intro k hk
  simp only [winv, List.mem_reverse, List.mem_map] at hk
  obtain ⟨a, ha, rfl⟩ := hk
  exact (move_facts (g2_lt (hw a ha))).2.2.2.2 (hw a ha)

theorem winv_winv {w : List Nat} (hw : ∀ k ∈ w, k < 18) : winv (winv w) = w := by
  unfold winv
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  conv => rhs; rw [← List.map_id w]
  apply List.map_congr_left
  intro a ha
  exact (move_facts (hw a ha)).2.2.2.1

theorem eval_winv : ∀ (w : List Nat), (∀ k ∈ w, k < 18) → eval (w ++ winv w) = St.id := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons m w ih =>
    intro hw
    have hm := move_facts (hw m (by simp))
    have hw' : ∀ k ∈ w, k < 18 := fun k hk => hw k (by simp [hk])
    have hwi := winv_lt hw'
    have h1 : (m :: w) ++ winv (m :: w) = m :: ((w ++ winv w) ++ [minv m]) := by
      rw [winv_cons]; simp
    have hall : ∀ k ∈ (w ++ winv w), k < 18 := all_append hw' hwi
    have hlast : ∀ k ∈ [minv m], k < 18 := by simp [hm.2.1]
    rw [h1, eval_cons (hw m (by simp)) (all_append hall hlast), eval_app hlast hall, ih hw',
      id_mul (valid_eval _ hlast)]
    have e1 : eval [minv m] = moves[minv m]! := by
      show apply St.id (minv m) = _
      rw [apply_eq, id_mul (move_facts hm.2.1).1]
    rw [e1, hm.2.2.1]

-- ---------- the superflip ----------
def sfFactsB : Bool := validB sfSt && sfSt.mul sfSt == St.id && eval superflip == sfSt &&
  superflip.all (fun m => decide (m < 18)) && superflip.length == 20 &&
  cpG.contains St.id.cp && epG.contains St.id.ep
theorem sfFacts_true : sfFactsB = true := by native_decide

theorem sf_parts : Valid sfSt ∧ sfSt.mul sfSt = St.id ∧ eval superflip = sfSt ∧ (∀ m ∈ superflip, m < 18) ∧
    superflip.length = 20 ∧ Dom idP := by
  have h := sfFacts_true; unfold sfFactsB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨valid_of_B h1, h2, h3, fun m hm => of_decide_eq_true ((List.all_eq_true.1 h4) m hm), h5, h6, h7⟩

theorem sfValid : Valid sfSt := sf_parts.1

theorem sfeo : ∀ i < 12, sfSt.eo[i]! = 1 := by decide

theorem sf_central {x : St} (hx : Valid x) : sfSt.mul x = x.mul sfSt := by
  obtain ⟨-, -, -, -, x5, -, x7, -⟩ := hx
  apply St.ext'
  · rw [mul_cp, mul_cp]; apply map_range_congr; intro i hi
    show St.id.cp[x.cp[i]!]! = x.cp[St.id.cp[i]!]!
    rw [idc _ (x5 i hi), idc i hi]
  · rw [mul_co, mul_co]; apply map_range_congr; intro i hi
    show (St.id.co[x.cp[i]!]! + x.co[i]!) % 3 = (x.co[St.id.cp[i]!]! + St.id.co[i]!) % 3
    rw [idco _ (x5 i hi), idc i hi, idco i hi]; omega
  · rw [mul_ep, mul_ep]; apply map_range_congr; intro i hi
    show St.id.ep[x.ep[i]!]! = x.ep[St.id.ep[i]!]!
    rw [ide _ (x7 i hi), ide i hi]
  · rw [mul_eo, mul_eo]; apply map_range_congr; intro i hi
    show (sfSt.eo[x.ep[i]!]! + x.eo[i]!) % 2 = (x.eo[St.id.ep[i]!]! + sfSt.eo[i]!) % 2
    rw [sfeo _ (x7 i hi), ide i hi, sfeo i hi]; omega

/-- a solution of the superflip can be rotated cyclically -/
theorem sol_rot {a b : List Nat} (ha : ∀ k ∈ a, k < 18) (hb : ∀ k ∈ b, k < 18) (h : eval (a ++ b) = sfSt) :
    eval (b ++ a) = sfSt := by
  have Va := valid_eval a ha
  have Vb := valid_eval b hb
  have hi := winv_lt ha
  rw [eval_app hb ha] at h
  rw [eval_app ha hb]
  have hinv : (eval (winv a)).mul (eval a) = St.id := by
    have e := eval_winv (winv a) hi
    rw [winv_winv ha, eval_app ha hi] at e; exact e
  calc (eval b).mul (eval a) = St.id.mul ((eval b).mul (eval a)) := (id_mul (valid_mul Vb Va)).symm
    _ = ((eval (winv a)).mul (eval a)).mul ((eval b).mul (eval a)) := by rw [hinv]
    _ = (eval (winv a)).mul ((eval a).mul ((eval b).mul (eval a))) := mul_assoc' _ Va (valid_mul Vb Va)
    _ = (eval (winv a)).mul (((eval a).mul (eval b)).mul (eval a)) := by rw [mul_assoc' _ Vb Va]
    _ = (eval (winv a)).mul (sfSt.mul (eval a)) := by rw [h]
    _ = (eval (winv a)).mul ((eval a).mul sfSt) := by rw [sf_central Va]
    _ = ((eval (winv a)).mul (eval a)).mul sfSt := (mul_assoc' _ Va sfValid).symm
    _ = sfSt := by rw [hinv, id_mul sfValid]

/-- solving the superflip from the superflip = evaluating to the superflip -/
theorem sol_iff {w : List Nat} (hw : ∀ k ∈ w, k < 18) : applyList sfSt w = St.id ↔ eval w = sfSt := by
  have Vw := valid_eval w hw
  rw [applyList_eq w hw _ sfValid]
  constructor
  · intro h
    calc eval w = St.id.mul (eval w) := (id_mul Vw).symm
      _ = (sfSt.mul sfSt).mul (eval w) := by rw [sf_parts.2.1]
      _ = sfSt.mul (sfSt.mul (eval w)) := mul_assoc' _ sfValid Vw
      _ = sfSt := by rw [h, mul_id sfValid]
  · intro h; rw [h, sf_parts.2.1]

-- ---------- conjugation by whole-cube rotations ----------
structure RotOK (T Ti : St) (μ : Nat → Nat) : Prop where
  vT : Valid T
  vTi : Valid Ti
  inv1 : T.mul Ti = St.id
  inv2 : Ti.mul T = St.id
  mv : ∀ m < 18, μ m < 18 ∧ (T.mul moves[m]!).mul Ti = moves[μ m]!
  fixsf : (T.mul sfSt).mul Ti = sfSt

def cj (T Ti x : St) : St := (T.mul x).mul Ti

theorem cj_mul {T Ti : St} {μ : Nat → Nat} (h : RotOK T Ti μ) {x y : St} (hx : Valid x) (hy : Valid y) :
    cj T Ti (x.mul y) = (cj T Ti x).mul (cj T Ti y) := by
  unfold cj
  have vTy := valid_mul h.vT hy
  calc (T.mul (x.mul y)).mul Ti = ((T.mul x).mul y).mul Ti := by rw [mul_assoc' _ hx hy]
    _ = (T.mul x).mul (y.mul Ti) := mul_assoc' _ hy h.vTi
    _ = (T.mul x).mul ((St.id.mul y).mul Ti) := by rw [id_mul hy]
    _ = (T.mul x).mul (((Ti.mul T).mul y).mul Ti) := by rw [h.inv2]
    _ = (T.mul x).mul ((Ti.mul (T.mul y)).mul Ti) := by rw [mul_assoc' _ h.vT hy]
    _ = (T.mul x).mul (Ti.mul ((T.mul y).mul Ti)) := by rw [mul_assoc' _ vTy h.vTi]
    _ = ((T.mul x).mul Ti).mul ((T.mul y).mul Ti) := (mul_assoc' _ h.vTi (valid_mul vTy h.vTi)).symm

theorem map_lt {μ : Nat → Nat} (hμ : ∀ m < 18, μ m < 18) {w : List Nat} (hw : ∀ k ∈ w, k < 18) :
    ∀ k ∈ w.map μ, k < 18 := by
  intro k hk; simp only [List.mem_map] at hk; obtain ⟨a, ha, rfl⟩ := hk; exact hμ a (hw a ha)

theorem cj_eval {T Ti : St} {μ : Nat → Nat} (h : RotOK T Ti μ) :
    ∀ w : List Nat, (∀ m ∈ w, m < 18) → cj T Ti (eval w) = eval (w.map μ) := by
  intro w
  induction w with
  | nil => intro _; show (T.mul St.id).mul Ti = St.id; rw [mul_id h.vT, h.inv1]
  | cons m w ih =>
    intro hw
    have hm := hw m (by simp)
    have hw' : ∀ k ∈ w, k < 18 := fun k hk => hw k (by simp [hk])
    have hμ : ∀ m < 18, μ m < 18 := fun m hm => (h.mv m hm).1
    rw [eval_cons hm hw', cj_mul h (move_facts hm).1 (valid_eval w hw'), ih hw', List.map_cons,
      eval_cons (h.mv m hm).1 (map_lt hμ hw')]
    unfold cj; rw [(h.mv m hm).2]

theorem sol_cj {T Ti : St} {μ : Nat → Nat} (h : RotOK T Ti μ) {w : List Nat} (hw : ∀ m ∈ w, m < 18)
    (hs : eval w = sfSt) : eval (w.map μ) = sfSt := by
  rw [← cj_eval h w hw, hs]; exact h.fixsf

-- ---------- H-words ----------
/-- a state solved by a word of ⟨U,D,R2,L2,F2,B2⟩ is that word's inverse -/
theorem eq_of_solved {x : St} (hx : Valid x) {v : List Nat} (hv : ∀ k ∈ v, k < 18) (h : applyList x v = St.id) :
    x = eval (winv v) := by
  have hvi := winv_lt hv
  rw [applyList_eq v hv _ hx] at h
  have e := eval_winv v hv
  rw [eval_app hvi hv] at e
  calc x = x.mul St.id := (mul_id hx).symm
    _ = x.mul ((eval v).mul (eval (winv v))) := by rw [e]
    _ = (x.mul (eval v)).mul (eval (winv v)) := (mul_assoc' _ (valid_eval v hv) (valid_eval _ hvi)).symm
    _ = eval (winv v) := by rw [h, id_mul (valid_eval _ hvi)]

theorem hform_of_solved {x : St} (hx : Valid x) {v : List Nat} (hv : ∀ k ∈ v, k ∈ g2Moves) (h : applyList x v = St.id) :
    rank x = i0 ∧ Dom (x.cp, x.ep) := by
  have hv18 : ∀ k ∈ v, k < 18 := fun k hk => g2_lt (hv k hk)
  have hx' := eq_of_solved hx hv18 h
  have hg := winv_g2 hv
  obtain ⟨e1, e2, e3⟩ := g2_keep (winv v) hg St.id rfl rfl rfl
  refine ⟨?_, ?_⟩
  · rw [hx']; unfold rank i0; unfold eval; rw [e1, e2, e3]
  · rw [hx']
    have := applyList_pact (winv v) St.id
    unfold eval; rw [this]
    have hd : ∀ W : List Nat, (∀ k ∈ W, k ∈ g2Moves) → ∀ p, Dom p → Dom (pActList p W) := by
      intro W
      induction W with
      | nil => intro _ p hp; exact hp
      | cons m W ih =>
        intro hW p hp
        rw [pActList_cons]
        exact ih (fun k hk => hW k (by simp [hk])) _ (dom_act hp (hW m (by simp)))
    exact hd _ hg _ sf_parts.2.2.2.2.2
