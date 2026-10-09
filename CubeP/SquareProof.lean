import CubeP.SquareThm
open Std

def HalfOnly (w : List Nat) : Prop := ∀ m ∈ w, m ∈ half

theorem applyList_nil (x : St) : applyList x [] = x := rfl
theorem applyList_cons (x : St) (h : Nat) (w : List Nat) : applyList x (h :: w) = applyList (apply x h) w := rfl

theorem sq_parts : ((sqTableF ()).toList.all (fun p => sqEntryOkW (sqTableF ()) p.1 p.2) = true) ∧ (sqTableF ())[St.id]? = some [] := by
  have h := sqCheck_true
  unfold sqCheckF sqCheckW at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, of_decide_eq_true h.2⟩

theorem sq_entry {x : St} {v : List Nat} (hx : (sqTableF ())[x]? = some v) : sqEntryOkW (sqTableF ()) x v = true := by
  have hall := sq_parts.1
  rw [List.all_eq_true] at hall
  have hm : (x, v) ∈ (sqTableF ()).toList := (HashMap.mem_toList_iff_getElem?_eq_some).2 hx
  exact hall (x, v) hm

theorem sq_entry_props {x : St} {v : List Nat} (hx : (sqTableF ())[x]? = some v) :
    HalfOnly v ∧ v.length ≤ 15 ∧ applyList St.id v = x ∧
    ∀ h ∈ half, ∃ v', (sqTableF ())[apply x h]? = some v' ∧ v'.length ≤ v.length + 1 := by
  have e := sq_entry hx
  unfold sqEntryOkW at e
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at e
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := e
  refine ⟨?_, of_decide_eq_true h2, of_decide_eq_true h3, ?_⟩
  · intro m hm
    have hc := (List.all_eq_true.1 h1) m hm
    exact List.contains_iff_mem.1 hc
  · intro h hh
    have hc := (List.all_eq_true.1 h4) h hh
    revert hc
    generalize (sqTableF ())[apply x h]? = q
    intro hc
    cases q with
    | none => exact absurd hc (by simp)
    | some v' => exact ⟨v', rfl, of_decide_eq_true hc⟩

theorem sq_reach (w : List Nat) (hw : HalfOnly w) :
    ∀ x v, (sqTableF ())[x]? = some v → ∃ v', (sqTableF ())[applyList x w]? = some v' ∧ v'.length ≤ v.length + w.length := by
  induction w with
  | nil => intro x v hx; exact ⟨v, by simpa [applyList_nil] using hx, by simp⟩
  | cons h w ih =>
    intro x v hx
    have hh : h ∈ half := hw h (by simp)
    have hw' : HalfOnly w := fun m hm => hw m (by simp [hm])
    obtain ⟨v1, hv1, hl1⟩ := (sq_entry_props hx).2.2.2 h hh
    obtain ⟨v2, hv2, hl2⟩ := ih hw' (apply x h) v1 hv1
    refine ⟨v2, by rw [applyList_cons]; exact hv2, ?_⟩
    simp only [List.length_cons]; omega

/-- Every element of the square group <U2,R2,F2,D2,L2,B2> can be written with at most 15 half turns. -/
theorem square_group_upper (w : List Nat) (hw : HalfOnly w) :
    ∃ w', HalfOnly w' ∧ w'.length ≤ 15 ∧ eval w' = eval w := by
  obtain ⟨v, hv, -⟩ := sq_reach w hw St.id [] sq_parts.2
  obtain ⟨h1, h2, h3, -⟩ := sq_entry_props hv
  exact ⟨v, h1, h2, h3⟩

/-- Lower bound: any half-turn word reaching a position has length at least its table distance. -/
theorem square_group_dist_le (w : List Nat) (hw : HalfOnly w) :
    ∃ v, (sqTableF ())[eval w]? = some v ∧ v.length ≤ w.length := by
  obtain ⟨v, hv, hl⟩ := sq_reach w hw St.id [] sq_parts.2
  exact ⟨v, hv, by simpa using hl⟩

theorem far_props : ∃ v, (sqTableF ())[eval farWord]? = some v ∧ v.length = 15 := by
  have h := farCheck_true
  unfold farCheckF farCheckW at h
  revert h
  generalize (sqTableF ())[eval farWord]? = q
  intro h
  cases q with
  | none => exact absurd h (by simp)
  | some v =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨v, rfl, h.1.1⟩

theorem farWord_half : HalfOnly farWord := by
  intro m hm
  have h := farCheck_true
  unfold farCheckF farCheckW at h
  revert h
  generalize (sqTableF ())[eval farWord]? = q
  intro h
  cases q with
  | none => exact absurd h (by simp)
  | some v =>
    simp only [Bool.and_eq_true] at h
    exact List.contains_iff_mem.1 ((List.all_eq_true.1 h.2) m hm)

/-- **God's number of the square group <U2,R2,F2,D2,L2,B2> is 15** (in half turns): every element has a word of
length ≤ 15, and the element reached by `farWord` has no shorter word. -/
theorem square_group_gods_number :
    (∀ w, HalfOnly w → ∃ w', HalfOnly w' ∧ w'.length ≤ 15 ∧ eval w' = eval w) ∧
    (HalfOnly farWord ∧ ∀ w, HalfOnly w → eval w = eval farWord → 15 ≤ w.length) := by
  refine ⟨square_group_upper, farWord_half, ?_⟩
  intro w hw he
  obtain ⟨v, hv, hl⟩ := square_group_dist_le w hw
  obtain ⟨v0, hv0, hl0⟩ := far_props
  rw [he, hv0] at hv
  cases hv
  omega

#print axioms square_group_gods_number
