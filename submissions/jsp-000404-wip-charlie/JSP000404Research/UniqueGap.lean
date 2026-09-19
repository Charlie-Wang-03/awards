import JSP000404Research.SharpDeficit
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Unique positive gap from unit support

This converts the indicator-sum definition of `positiveSupport` into an
actual unique index.  It is the final finite-combinatorial step needed before
choosing the exceptional gap of an `ell = 1` centre.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Finite set of quotient gaps with positive integer part. -/
noncomputable def positiveIndices
    {I : Type*} [Fintype I] (q : I → ℕ) : Finset I := by
  classical
  exact Finset.univ.filter fun i ↦ q i ≠ 0

theorem card_positiveIndices_eq_support
    {I : Type*} [Fintype I] (q : I → ℕ) :
    (positiveIndices q).card = positiveSupport q := by
  classical
  unfold positiveIndices positiveSupport
  have h := Finset.card_filter (fun i : I ↦ q i ≠ 0) (Finset.univ : Finset I)
  simpa using h

/-- Support count one means there is a unique positive quotient gap. -/
theorem existsUnique_positive_of_support_one
    {I : Type*} [Fintype I] (q : I → ℕ)
    (hsupport : positiveSupport q = 1) :
    ∃! i, q i ≠ 0 := by
  classical
  have hcard : (positiveIndices q).card = 1 := by
    rw [card_positiveIndices_eq_support q, hsupport]
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_, ?_⟩
  · have himem : i ∈ positiveIndices q := by
      rw [hi]
      simp
    simpa [positiveIndices] using himem
  · intro j hj
    have hjmem : j ∈ positiveIndices q := by
      simp [positiveIndices, hj]
    rw [hi] at hjmem
    simpa using hjmem

/-- A unit Sendov deficit therefore singles out one and only one positive
integer quotient gap. -/
theorem unit_deficit_existsUnique_positive
    {I : Type*} [Fintype I] (q : I → ℕ) (n : ℕ)
    (hn : 2 ≤ n)
    (hQ : (∑ i, q i) ≤ n)
    (hell : n - floorExcess q = 1) :
    ∃! i, q i ≠ 0 := by
  exact existsUnique_positive_of_support_one q
    (unit_deficit_structure q n hn hQ hell).1

#print axioms card_positiveIndices_eq_support
#print axioms existsUnique_positive_of_support_one
#print axioms unit_deficit_existsUnique_positive

end JSP000404Research
