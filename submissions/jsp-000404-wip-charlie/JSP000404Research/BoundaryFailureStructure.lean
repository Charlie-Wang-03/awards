import JSP000404Research.BoundaryDominance
import Mathlib.Tactic

/-!
# Exact structure of a local phase-budget failure

Assume the one-exception domination for a phase boundary-count vector:

  q i <= b i       for i != e,
  q e <= b e + 1.

If the local active-colour budget nevertheless fails, then the exceptional
gap must realize the entire possible one-unit loss.

Concretely:

  q e = b e + 1,
  1 <= b e,
  2 <= q e,

and globally

  floorExcess q = floorExcess b + 1.

Thus a bad phase cannot be caused by a sub-unit or merely unit-sized
exceptional gap.  The unique long partition spacing must sit inside a ray gap
whose natural quotient is at least two.
-/

namespace JSP000404Research

open scoped BigOperators

/-- If all regular gaps dominate and the exceptional gap also satisfies
q e <= b e, then the exact local budget holds. -/
theorem support_budget_of_exception_not_lost
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (he : q e ≤ b e) :
    positiveSupport b ≤ n - floorExcess q := by
  apply support_le_deficit_of_full_domination q b n hsum
  intro i
  by_cases hie : i = e
  · subst i
    exact he
  · exact hregular i hie

/-- Strict budget failure forces the exceptional quotient to be exactly one
larger than its boundary count. -/
theorem exceptional_eq_boundary_add_one_of_budget_failure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    q e = b e + 1 := by
  by_contra hne
  have he : q e ≤ b e := by
    omega
  have hgood :=
    support_budget_of_exception_not_lost
      q b e n hsum hregular he
  omega

/-- If the exceptional boundary count were zero, q e = 1 would contribute no
floor excess, so no budget failure could occur. -/
theorem exceptional_boundary_pos_of_budget_failure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    1 ≤ b e := by
  have heq :=
    exceptional_eq_boundary_add_one_of_budget_failure
      q b e n hsum hregular hexception hbad
  by_contra hnot
  have hb0 : b e = 0 := by omega
  have hqe : q e = 1 := by omega
  have hpoint :
      ∀ i : I, q i - 1 ≤ b i - 1 := by
    intro i
    by_cases hie : i = e
    · subst i
      simp [hqe, hb0]
    · have h := hregular i hie
      omega
  have hexcess : floorExcess q ≤ floorExcess b := by
    unfold floorExcess
    exact Finset.sum_le_sum fun i _ => hpoint i
  have hfail :=
    (support_budget_fails_iff_floorExcess_lt q b n hsum).1 hbad
  omega

/-- Therefore the exceptional quotient is at least two. -/
theorem exceptional_quotient_two_le_of_budget_failure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    2 ≤ q e := by
  have heq :=
    exceptional_eq_boundary_add_one_of_budget_failure
      q b e n hsum hregular hexception hbad
  have hbpos :=
    exceptional_boundary_pos_of_budget_failure
      q b e n hsum hregular hexception hbad
  omega

/-- The total floor-excess loss is then exactly one. -/
theorem floorExcess_eq_add_one_of_budget_failure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    floorExcess q = floorExcess b + 1 := by
  have hlower :=
    (support_budget_fails_iff_floorExcess_lt q b n hsum).1 hbad
  have hupper :=
    floorExcess_le_add_one_of_one_exception
      q b e hregular hexception
  omega

#print axioms support_budget_of_exception_not_lost
#print axioms exceptional_eq_boundary_add_one_of_budget_failure
#print axioms exceptional_boundary_pos_of_budget_failure
#print axioms exceptional_quotient_two_le_of_budget_failure
#print axioms floorExcess_eq_add_one_of_budget_failure

end JSP000404Research
