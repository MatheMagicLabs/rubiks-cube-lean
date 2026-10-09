import Cube.SwapLemmas

theorem nodup_adj_ne : ∀ (k : Nat) (l : List Nat), l.Nodup → k + 1 < l.length → l[k]! ≠ l[k+1]! := by
  intro k
  induction k with
  | zero =>
    intro l hn hl
    match l, hl with
    | a :: b :: t, _ =>
      have h1 := (List.nodup_cons.1 hn).1
      have : a ≠ b := fun h => h1 (by simp [h])
      simpa using this
  | succ k ih =>
    intro l hn hl
    match l, hl with
    | a :: t, hl =>
      have := ih t (List.nodup_cons.1 hn).2 (by simp at hl; omega)
      simpa using this

theorem swaps_cons (k : Nat) (ks l : List Nat) : swaps (k :: ks) l = swaps ks (swapAt k l) := rfl

theorem swaps_perm : ∀ (ks l : List Nat), (swaps ks l).Perm l := by
  intro ks
  induction ks with
  | nil => intro l; exact List.Perm.refl _
  | cons k ks ih => intro l; rw [swaps_cons]; exact (ih _).trans (swapAt_perm k l)

theorem inv_swaps : ∀ (ks l : List Nat), l.Nodup → (∀ k ∈ ks, k + 1 < l.length) →
    inv (swaps ks l) % 2 = (inv l + ks.length) % 2 := by
  intro ks
  induction ks with
  | nil => intro l _ _; simp [swaps]
  | cons k ks ih =>
    intro l hn hk
    rw [swaps_cons]
    have hk0 : k + 1 < l.length := hk k (by simp)
    have h1 := inv_swapAt k l hk0 (nodup_adj_ne k l hn hk0)
    have hn' : (swapAt k l).Nodup := hn.perm (swapAt_perm k l).symm
    have h2 := ih (swapAt k l) hn' (by intro k' hk'; rw [swapAt_length]; exact hk k' (by simp [hk']))
    simp only [List.length_cons]
    omega

def ksOk : Bool := (List.range 18).all (fun m =>
  (ksC[m]!).all (fun k => decide (k + 1 < 8)) && (ksE[m]!).all (fun k => decide (k + 1 < 12)) &&
  decide (((ksC[m]!).length + (ksE[m]!).length) % 2 = 0))
theorem ksOk_true : ksOk = true := by decide

theorem ks_props (m : Nat) (hm : m < 18) :
    (∀ k ∈ ksC[m]!, k + 1 < 8) ∧ (∀ k ∈ ksE[m]!, k + 1 < 12) ∧ ((ksC[m]!).length + (ksE[m]!).length) % 2 = 0 := by
  have h := ksOk_true
  unfold ksOk at h
  have hm' := (List.all_eq_true.1 h) m (List.mem_range.2 hm)
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hm'
  exact ⟨hm'.1.1, hm'.1.2, hm'.2⟩

/-- the parity law and the permutation invariants of reachable positions -/
def Good (x : St) : Prop :=
  x.cp.size = 8 ∧ x.ep.size = 12 ∧ x.cp.toList.Perm (List.range 8) ∧ x.ep.toList.Perm (List.range 12) ∧
  (inv x.cp.toList + inv x.ep.toList) % 2 = 0

theorem apply_cp_list (x : St) (m : Nat) :
    (apply x m).cp.toList = ((List.range 8).toArray.map (fun i => x.cp[(moves[m]!).cp[i]!]!)).toList := rfl
theorem apply_ep_list (x : St) (m : Nat) :
    (apply x m).ep.toList = ((List.range 12).toArray.map (fun i => x.ep[(moves[m]!).ep[i]!]!)).toList := rfl

theorem good_apply (x : St) (m : Nat) (hm : m < 18) (hx : Good x) : Good (apply x m) := by
  obtain ⟨hc, he, hpc, hpe, hpar⟩ := hx
  obtain ⟨kc, ke, kp⟩ := ks_props m hm
  have ec := cp_swaps m hm x.cp hc
  have ee := ep_swaps m hm x.ep he
  have lc : x.cp.toList.length = 8 := by simpa using hc
  have le : x.ep.toList.length = 12 := by simpa using he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [apply, St.mul, Array.size_map, List.size_toArray, List.length_range]
  · simp only [apply, St.mul, Array.size_map, List.size_toArray, List.length_range]
  · rw [apply_cp_list, ec]; exact (swaps_perm _ _).trans hpc
  · rw [apply_ep_list, ee]; exact (swaps_perm _ _).trans hpe
  · rw [apply_cp_list, ec, apply_ep_list, ee]
    have nc : x.cp.toList.Nodup := (List.nodup_range).perm hpc.symm
    have ne : x.ep.toList.Nodup := (List.nodup_range).perm hpe.symm
    have h1 := inv_swaps _ _ nc (by intro k hk; rw [lc]; exact kc k hk)
    have h2 := inv_swaps _ _ ne (by intro k hk; rw [le]; exact ke k hk)
    omega

theorem good_id : Good St.id := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact List.Perm.refl _
  · exact List.Perm.refl _
  · decide

theorem good_applyList (w : List Nat) (hw : ∀ m ∈ w, m < 18) : ∀ x, Good x → Good (applyList x w) := by
  induction w with
  | nil => intro x hx; exact hx
  | cons h w ih =>
    intro x hx
    show Good (applyList (apply x h) w)
    exact ih (fun m hm => hw m (by simp [hm])) _ (good_apply x h (hw h (by simp)) hx)

/-- **Parity law**: every reachable position has corner and edge permutations of equal parity. -/
theorem parity_law (w : List Nat) (hw : ∀ m ∈ w, m < 18) : Good (eval w) :=
  good_applyList w hw St.id good_id

#print axioms parity_law
