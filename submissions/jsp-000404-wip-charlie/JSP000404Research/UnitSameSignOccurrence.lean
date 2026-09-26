import JSP000404Research.SixPointUnitGapBudget
import JSP000404Research.HiddenSameSignQuotient
import JSP000404Research.SupportListBridge
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Duplicate unit quotients leave a same-sign unit in a one-transition path

At the n=4 six-point equality terminal every minimum centre has exactly two
unit quotients.  If one such centre has only one sign transition and that
transition quotient is 1, the second unit quotient cannot occur at the same
distinguished transition position.  Hence it lies inside one of the two
constant-sign blocks and is a same-sign unit occurrence.

This file isolates the list counting and the finite-function/list bridge.
-/

namespace JSP000404Research

/-- Number of entries equal to one in a natural-number list. -/
def listUnitCount : List ℕ → ℕ
  | [] => 0
  | q :: qs => (if q = 1 then 1 else 0) + listUnitCount qs

theorem listUnitCount_append
    (xs ys : List ℕ) :
    listUnitCount (xs ++ ys) =
      listUnitCount xs + listUnitCount ys := by
  induction xs with
  | nil =>
      simp [listUnitCount]
  | cons x xs ih =>
      simp [listUnitCount, ih, add_assoc]

/-- Canonical list representation preserves the number of unit coordinates. -/
theorem listUnitCount_ofFn_eq_unitSupport
    {m : ℕ} (q : Fin m → ℕ) :
    listUnitCount (List.ofFn q) = unitSupport q := by
  induction m with
  | zero =>
      simp [listUnitCount, unitSupport]
  | succ m ih =>
      rw [List.ofFn_succ]
      unfold listUnitCount unitSupport
      rw [Fin.sum_univ_succ]
      have htail :=
        ih (fun i : Fin m => q i.succ)
      unfold unitSupport at htail
      rw [htail]
      rfl

theorem centre_listUnitCount_eq_unitSupport
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ) :
    listUnitCount (quotientList t C.gaps) =
      unitSupport (centreQuotient C t) := by
  rw [← centreQuotient_ofFn C t]
  exact listUnitCount_ofFn_eq_unitSupport
    (centreQuotient C t)

/-- If pre ++ [1] ++ post contains exactly two unit entries, one further unit
lies in pre or post. -/
theorem extra_unit_mem_side_of_two_units
    (pre post : List ℕ)
    (hcount :
      listUnitCount (pre ++ 1 :: post) = 2) :
    1 ∈ pre ∨ 1 ∈ post := by
  rw [listUnitCount_append] at hcount
  simp only [listUnitCount] at hcount
  have hside :
      listUnitCount pre + listUnitCount post = 1 := by
    omega
  by_cases hpre : 1 ∈ pre
  · exact Or.inl hpre
  · right
    by_contra hpost
    have hpre0 : listUnitCount pre = 0 := by
      induction pre with
      | nil => rfl
      | cons q qs ih =>
          have hq : q ≠ 1 := by
            intro h
            apply hpre
            simp [h]
          have htail : 1 ∉ qs := by
            intro h
            apply hpre
            simp [h]
          simp [listUnitCount, hq, ih htail]
    have hpost0 : listUnitCount post = 0 := by
      induction post with
      | nil => rfl
      | cons q qs ih =>
          have hq : q ≠ 1 := by
            intro h
            apply hpost
            simp [h]
          have htail : 1 ∉ qs := by
            intro h
            apply hpost
            simp [h]
          simp [listUnitCount, hq, ih htail]
    omega

/-- Any quotient occurring in the left constant-sign block is a same-sign
occurrence. -/
theorem sameSignQuotientOccurs_of_mem_pre
    (q : ℕ) (a : Bool)
    (pre post : List ℕ) (qe : ℕ)
    (hq : q ∈ pre) :
    SameSignQuotientOccurs q a
      (List.replicate pre.length a ++
        List.replicate (post.length + 1) (!a))
      (pre ++ qe :: post) := by
  induction pre generalizing a with
  | nil =>
      simp at hq
  | cons r rs ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, List.mem_cons] at hq ⊢
      rcases hq with hr | htail
      · left
        exact ⟨hr.symm, rfl⟩
      · right
        exact ih a htail

/-- Any quotient occurring in the right constant-sign block is a same-sign
occurrence, regardless of the value of the distinguished transition quotient. -/
theorem sameSignQuotientOccurs_of_mem_post
    (q : ℕ) (a : Bool)
    (pre post : List ℕ) (qe : ℕ)
    (hq : q ∈ post) :
    SameSignQuotientOccurs q a
      (List.replicate pre.length a ++
        List.replicate (post.length + 1) (!a))
      (pre ++ qe :: post) := by
  induction pre generalizing a with
  | nil =>
      simp only [List.length_nil, List.replicate_zero,
        List.nil_append, List.replicate_succ,
        List.cons_append, TransitionQuotientOccurs,
        SameSignQuotientOccurs]
      right
      exact sameSignQuotientOccurs_replicate q (!a) post hq
  | cons r rs ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, SameSignQuotientOccurs]
      right
      exact ih a hq

/-- Two unit entries plus a distinguished unit transition force another unit
on a same-sign step. -/
theorem sameSign_unit_occurs_of_two_units_one_transition
    (a : Bool)
    (pre post : List ℕ)
    (hcount :
      listUnitCount (pre ++ 1 :: post) = 2) :
    SameSignQuotientOccurs 1 a
      (List.replicate pre.length a ++
        List.replicate (post.length + 1) (!a))
      (pre ++ 1 :: post) := by
  rcases extra_unit_mem_side_of_two_units
      pre post hcount with hpre | hpost
  · exact sameSignQuotientOccurs_of_mem_pre
      1 a pre post 1 hpre
  · exact sameSignQuotientOccurs_of_mem_post
      1 a pre post 1 hpost

theorem listUnitCount_pos_iff_one_mem
    (qs : List ℕ) :
    0 < listUnitCount qs ↔ 1 ∈ qs := by
  induction qs with
  | nil =>
      simp [listUnitCount]
  | cons q qs ih =>
      by_cases hq : q = 1
      · subst q
        simp [listUnitCount]
      · simp [listUnitCount, hq, ih]

/-- General form: if a one-transition decomposition contains exactly two unit
quotients, at least one unit lies in a constant-sign side block, irrespective
of the distinguished transition quotient value. -/
theorem sameSign_unit_occurs_of_two_units_two_blocks
    (a : Bool)
    (pre post : List ℕ)
    (qe : ℕ)
    (hcount :
      listUnitCount (pre ++ qe :: post) = 2) :
    SameSignQuotientOccurs 1 a
      (List.replicate pre.length a ++
        List.replicate (post.length + 1) (!a))
      (pre ++ qe :: post) := by
  by_cases hqe : qe = 1
  · subst qe
    exact sameSign_unit_occurs_of_two_units_one_transition
      a pre post hcount
  · rw [listUnitCount_append] at hcount
    simp [listUnitCount, hqe] at hcount
    have hside :
        0 < listUnitCount pre ∨
          0 < listUnitCount post := by
      omega
    rcases hside with hpre | hpost
    · have hmem :
          1 ∈ pre :=
        (listUnitCount_pos_iff_one_mem pre).1 hpre
      exact sameSignQuotientOccurs_of_mem_pre
        1 a pre post qe hmem
    · have hmem :
          1 ∈ post :=
        (listUnitCount_pos_iff_one_mem post).1 hpost
      exact sameSignQuotientOccurs_of_mem_post
        1 a pre post qe hmem

#print axioms listUnitCount_ofFn_eq_unitSupport
#print axioms centre_listUnitCount_eq_unitSupport
#print axioms extra_unit_mem_side_of_two_units
#print axioms sameSign_unit_occurs_of_two_units_one_transition

end JSP000404Research
