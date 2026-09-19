import JSP000404Research.BoundaryExcess
import Mathlib.Tactic

/-!
# One-exception domination of phase boundary counts

The rotating n-boundary partition has n-1 ordinary unit spacings and one
special spacing of length 1+delta.  For a cyclic family of geometric ray gaps,
the intended one-dimensional counting lemma is therefore:

* every ray gap not containing the special spacing receives at least its
  natural quotient q i of partition boundaries;
* the unique exceptional ray gap may receive one fewer boundary.

Abstractly, if b is the boundary-count vector and e is the exceptional gap,

  q i <= b i       for i != e,
  q e <= b e + 1.

This file proves the exact arithmetic consequence:

  floorExcess q <= floorExcess b + 1.

Combined with BoundaryExcess, every phase then has local active-colour count
at most ell+1.  The remaining geometric task is only to establish the
one-exception domination for actual circular intervals.
-/

namespace JSP000404Research

open scoped BigOperators

/-- Pointwise one-exception domination controls the total floor-excess loss by
one unit. -/
theorem floorExcess_le_add_one_of_one_exception
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1) :
    floorExcess q ≤ floorExcess b + 1 := by
  classical
  unfold floorExcess
  have hpoint :
      ∀ i : I,
        q i - 1 ≤ (b i - 1) + (if i = e then 1 else 0) := by
    intro i
    by_cases hie : i = e
    · subst i
      simp
      omega
    · simp [hie]
      have h := hregular i hie
      omega
  have hsum :
      (∑ i, (q i - 1)) ≤
        ∑ i, ((b i - 1) + (if i = e then 1 else 0)) :=
    Finset.sum_le_sum fun i _ => hpoint i
  rw [Finset.sum_add_distrib] at hsum
  have hindicator :
      (∑ i : I, (if i = e then 1 else 0)) = 1 := by
    simp
  rw [hindicator] at hsum
  exact hsum

/-- Boundary-budget consequence: under one-exception domination and total
boundary mass n, the active support is at most ell+1. -/
theorem support_le_deficit_add_one_of_one_exception
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1) :
    positiveSupport b ≤ n - floorExcess q + 1 := by
  apply support_le_deficit_add_one_of_excess_loss_le_one q b n hsum
  exact floorExcess_le_add_one_of_one_exception
    q b e hregular hexception

/-- If even the exceptional gap meets its full quotient, the exact local
budget follows. -/
theorem support_le_deficit_of_full_domination
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hdom : ∀ i, q i ≤ b i) :
    positiveSupport b ≤ n - floorExcess q := by
  apply (support_budget_iff_floorExcess_le q b n hsum).2
  unfold floorExcess
  exact Finset.sum_le_sum fun i _ => by
    have h := hdom i
    omega

#print axioms floorExcess_le_add_one_of_one_exception
#print axioms support_le_deficit_add_one_of_one_exception
#print axioms support_le_deficit_of_full_domination

end JSP000404Research
