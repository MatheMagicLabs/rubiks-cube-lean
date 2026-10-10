import CubeP.Ord11Thm
import CubeP.Kph1Proof
open Std

/-! **Elements of order 11 need at least 10 face turns, and 10 suffice.**
Group theory (by hand): `g^11 = 1` forces the corner permutation to be trivial (cycle lengths divide 11 and are ≤ 8)
and then the corner twists to vanish (11 is a unit mod 3). Here both facts are finite checks; the search over all
words of length ≤ 9 is pruned by a 1-Lipschitz corner distance table. -/

theorem ordc_parts : cpClosed = true ∧ cpSet.contains St.id.cp = true ∧ tabOk cpL cpIdx cpAct TP 40320 St.id.cp = true ∧
    cpL.all (fun p => permPow p 11 != St.id.cp || p == St.id.cp) = true ∧
    coL.all (fun c => coPow c 11 != St.id.co || c == St.id.co) = true := by
  have h := ordComp_true; unfold ordCompF at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
  exact ⟨a, b, c, d, e⟩

def InCo (x : St) : Prop := cpSet.contains x.cp = true ∧ coSet.contains x.co = true

theorem inCo_apply {x : St} (hx : InCo x) (m : Nat) (hm : m < 18) : InCo (apply x m) := by
  refine ⟨?_, ?_⟩
  · rw [apply_cp]; exact closed_step (by have := ordc_parts.1; unfold cpClosed at this; exact this) hx.1 m hm
  · rw [apply_co]; exact closed_step (by have := comp_parts.2.1; unfold coClosed at this; exact this) hx.2 m hm

theorem inCo_applyList (w : List Nat) (hw : ∀ m ∈ w, m < 18) : ∀ x, InCo x → InCo (applyList x w) := by
  induction w with
  | nil => intro x hx; exact hx
  | cons h w ih =>
    intro x hx; rw [applyList_cons']
    exact ih (fun m hm => hw m (by simp [hm])) _ (inCo_apply hx h (hw h (by simp)))

theorem inCo_id : InCo St.id := ⟨ordc_parts.2.1, comp_parts.2.2.2.2.1⟩

theorem crank_apply (x : St) (hx : InCo x) (m : Nat) (hm : m < 18) : crank (apply x m) = cnext (crank x) m := by
  obtain ⟨rp, hp, hrp, hmp, -⟩ := tab_fact ordc_parts.2.2.1 (mem_L hx.1)
  obtain ⟨rc, hc, hrc, hmc, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.1 (mem_L hx.2)
  unfold crank cnext
  rw [apply_cp, apply_co, bang_of (hmp m hm), bang_of (hmc m hm), bang_of hp, bang_of hc]
  have e1 : (rp * 2187 + rc) / 2187 = rp := by omega
  have e2 : (rp * 2187 + rc) % 2187 = rc := by omega
  rw [e1, e2]

theorem crank_lt (x : St) (hx : InCo x) : crank x < NCR := by
  obtain ⟨rp, hp, hrp, -, -⟩ := tab_fact ordc_parts.2.2.1 (mem_L hx.1)
  obtain ⟨rc, hc, hrc, -, -⟩ := tab_fact comp_parts.2.2.2.2.2.2.2.1 (mem_L hx.2)
  unfold crank NCR; rw [bang_of hp, bang_of hc]; omega

theorem clipFrom_spec (d : ByteArray) : ∀ n, clipFrom d n = true → ∀ i < n, clipCell d i = true := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    unfold clipFrom at h
    split at h
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact ih h i h'
      · subst h'; assumption
    · exact absurd h (by simp)

theorem o11_parts : clipFrom (cdistF ()) NCR = true ∧ ((cdistF ()).get! c0).toNat = 0 ∧
    dfs11 (cdistF ()) St.id (crank St.id) 9 = true := by
  have h := ord11_true; unfold ord11F at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem clip_step (x : St) (hx : InCo x) (m : Nat) (hm : m < 18) :
    ((cdistF ()).get! (crank x)).toNat ≤ ((cdistF ()).get! (crank (apply x m))).toNat + 1 := by
  have h := clipFrom_spec _ _ o11_parts.1 (crank x) (crank_lt x hx)
  unfold clipCell at h
  have := (List.all_eq_true.1 h) m (List.mem_range.2 hm)
  rw [crank_apply x hx m hm]
  exact of_decide_eq_true this

theorem clip_reach (w : List Nat) (hw : ∀ m ∈ w, m < 18) : ∀ x, InCo x →
    ((cdistF ()).get! (crank x)).toNat ≤ ((cdistF ()).get! (crank (applyList x w))).toNat + w.length := by
  induction w with
  | nil => intro x _; simp [applyList]
  | cons h w ih =>
    intro x hx
    have h1 := clip_step x hx h (hw h (by simp))
    have h2 := ih (fun m hm => hw m (by simp [hm])) (apply x h) (inCo_apply hx h (hw h (by simp)))
    rw [applyList_cons']
    simp only [List.length_cons]; omega

/-! powers -/
theorem cp_pow (x : St) : ∀ n, (stPow x n).cp = permPow x.cp n
  | 0 => rfl
  | n + 1 => by
    show (List.range 8).toArray.map (fun i => (stPow x n).cp[x.cp[i]!]!) =
      (List.range 8).toArray.map (fun i => (permPow x.cp n)[x.cp[i]!]!)
    rw [cp_pow x n]

theorem co_pow (x : St) (hx : x.cp = St.id.cp) : ∀ n, (stPow x n).co = coPow x.co n
  | 0 => rfl
  | n + 1 => by
    show (List.range 8).toArray.map (fun i => ((stPow x n).co[x.cp[i]!]! + x.co[i]!) % 3) =
      (List.range 8).toArray.map (fun i => ((coPow x.co n)[St.id.cp[i]!]! + x.co[i]!) % 3)
    rw [co_pow x hx n, hx]

/-- an element of order 11 has its corners solved -/
theorem ord11_corners (x : St) (hx : InCo x) (h : isOrd11 x = true) : cSolved x = true := by
  unfold isOrd11 at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  have hp : permPow x.cp 11 = St.id.cp := by rw [← cp_pow x 11, h.2]
  have h4 := (List.all_eq_true.1 ordc_parts.2.2.2.1) x.cp (mem_L hx.1)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h4
  have hcp : x.cp = St.id.cp := by
    rcases h4 with h4 | h4
    · exact absurd hp h4
    · exact h4
  have hc : coPow x.co 11 = St.id.co := by rw [← co_pow x hcp 11, h.2]
  have h5 := (List.all_eq_true.1 ordc_parts.2.2.2.2) x.co (mem_L hx.2)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h5
  have hco : x.co = St.id.co := by
    rcases h5 with h5 | h5
    · exact absurd hc h5
    · exact h5
  unfold cSolved; rw [hcp, hco]; simp

theorem crank_solved (x : St) (h : cSolved x = true) : crank x = c0 := by
  unfold cSolved at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold crank c0; rw [h.1, h.2]

theorem dfs11_spec : ∀ n x, InCo x → dfs11 (cdistF ()) x (crank x) n = true →
    ∀ v : List Nat, v.length ≤ n → (∀ m ∈ v, m < 18) → isOrd11 (applyList x v) = false := by
  intro n
  induction n with
  | zero =>
    intro x hx hd v hv _
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hv0
    unfold dfs11 at hd
    show isOrd11 x = false
    cases ho : isOrd11 x
    · rfl
    · rw [ho, ord11_corners x hx ho] at hd; simp at hd
  | succ n ih =>
    intro x hx hd v hv hvm
    unfold dfs11 at hd
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
    obtain ⟨hself, hall⟩ := hd
    cases v with
    | nil =>
      show isOrd11 x = false
      cases ho : isOrd11 x
      · rfl
      · rw [ho, ord11_corners x hx ho] at hself; simp at hself
    | cons m v' =>
      have hm : m < 18 := hvm m (by simp)
      have hc := (List.all_eq_true.1 hall) m (List.mem_range.2 hm)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rw [← crank_apply x hx m hm] at hc
      have hx' := inCo_apply hx m hm
      have hvm' : ∀ k ∈ v', k < 18 := fun k hk => hvm k (by simp [hk])
      have hlen : v'.length ≤ n := by simp at hv; omega
      rw [applyList_cons']
      rcases hc with hp | hrec
      · cases ho : isOrd11 (applyList (apply x m) v')
        · rfl
        · exfalso
          have hy : InCo (applyList (apply x m) v') := inCo_applyList _ hvm' _ hx'
          have hs := crank_solved _ (ord11_corners _ hy ho)
          have hr := clip_reach v' hvm' (apply x m) hx'
          rw [hs, o11_parts.2.1] at hr
          omega
      · exact ih (apply x m) hx' hrec v' hlen hvm'

/-- **Every word producing an element of order 11 has at least 10 face turns.** -/
theorem order11_lower (w : List Nat) (hw : ∀ m ∈ w, m < 18) (h : isOrd11 (eval w) = true) : 10 ≤ w.length := by
  rcases Nat.lt_or_ge w.length 10 with hlt | hge
  · have := dfs11_spec 9 St.id inCo_id o11_parts.2.2 w (by omega) hw
    unfold eval at h
    rw [this] at h; exact absurd h (by simp)
  · exact hge

/-- **...and 10 suffice:** `U R U F R' L U' R' F' D'` has order 11. -/
theorem order11_witness : ord11Word.length = 10 ∧ (∀ m ∈ ord11Word, m < 18) ∧ isOrd11 (eval ord11Word) = true := by
  have h := ord11Wit_true; unfold ord11WitF at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, fun m hm => of_decide_eq_true ((List.all_eq_true.1 h.1.2) m hm), h.2⟩

#print axioms order11_lower
#print axioms order11_witness
