import Cube.Model

/-! Permutation parity via inversions on lists, adjacent swaps, and the cube's parity law. -/

def ltCount (c : Nat) : List Nat → Nat
  | [] => 0
  | x :: t => (if x < c then 1 else 0) + ltCount c t

def inv : List Nat → Nat
  | [] => 0
  | a :: t => ltCount a t + inv t

/-- swap the entries at positions k and k+1 -/
def swapAt : Nat → List Nat → List Nat
  | 0, a :: b :: t => b :: a :: t
  | k + 1, a :: t => a :: swapAt k t
  | _, l => l

theorem ltCount_swapAt (c : Nat) : ∀ (k : Nat) (l : List Nat), ltCount c (swapAt k l) = ltCount c l := by
  intro k
  induction k with
  | zero =>
    intro l
    match l with
    | [] => rfl
    | [a] => rfl
    | a :: b :: t => simp only [swapAt, ltCount]; omega
  | succ k ih =>
    intro l
    match l with
    | [] => rfl
    | a :: t => simp only [swapAt, ltCount, ih]

/-- adjacent swap of two distinct entries flips the inversion parity -/
theorem inv_swapAt : ∀ (k : Nat) (l : List Nat), k + 1 < l.length → l[k]! ≠ l[k+1]! →
    inv (swapAt k l) % 2 = (inv l + 1) % 2 := by
  intro k
  induction k with
  | zero =>
    intro l hl hne
    match l, hl with
    | a :: b :: t, _ =>
      simp only [swapAt, inv, ltCount]
      have : a ≠ b := by simpa using hne
      by_cases h : a < b
      · have h2 : ¬ b < a := by omega
        simp only [h, h2, if_true, if_false]; omega
      · have h2 : b < a := by omega
        simp only [h, h2, if_true, if_false]; omega
  | succ k ih =>
    intro l hl hne
    match l, hl with
    | a :: t, hl =>
      simp only [swapAt, inv, ltCount_swapAt]
      have := ih t (by simp at hl; omega) (by simpa using hne)
      omega

theorem swapAt_perm : ∀ (k : Nat) (l : List Nat), (swapAt k l).Perm l := by
  intro k
  induction k with
  | zero => intro l; match l with
    | [] => exact List.Perm.refl _
    | [a] => exact List.Perm.refl _
    | a :: b :: t => exact List.Perm.swap a b t
  | succ k ih => intro l; match l with
    | [] => exact List.Perm.refl _
    | a :: t => exact List.Perm.cons a (ih t)

theorem swapAt_length : ∀ (k : Nat) (l : List Nat), (swapAt k l).length = l.length :=
  fun k l => (swapAt_perm k l).length_eq

def swaps (ks : List Nat) (l : List Nat) : List Nat := ks.foldl (fun acc k => swapAt k acc) l
