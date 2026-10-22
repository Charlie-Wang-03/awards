import JSP000404Research.ThreeFiveNextSupportTwoRigidity
import JSP000404Research.SixPointUnitGapBudget
import Mathlib.Tactic

/-!
# Exact two-plus-one quotient shape of a saturated next-layer centre

The genuine n=3 no-top four-next motif contains at least two
support-two centres with floor excess one. Such a centre has
total quotient mass three with support two. Its nonzero quotient
values are necessarily 2 and 1, one of each.

This closes the discrete *multiplicity* of those two supports,
not the geometric non-realizability of the no-top motif.
-/

namespace JSP000404Research

open scoped BigOperators

/-- For a quotient vector taking values only 0,1,2, the floor excess
counts precisely its coordinates of value two. -/
theorem floorExcess_eq_nonUnitPositiveSupport_of_le_two
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hbound : ∀ i, q i ≤ 2) :
    floorExcess q = nonUnitPositiveSupport q := by
  classical
  unfold floorExcess nonUnitPositiveSupport
  apply Finset.sum_congr rfl
  intro i _
  have hi := hbound i
  interval_cases h : q i <;> simp [h]

/-- Exponent one and support two force exactly one unit entry
and exactly one double entry. -/
theorem unit_and_double_counts_of_excess_one_support_two
    {I : Type*} [Fintype I]
    (q : I → ℕ)
    (hEx : floorExcess q = 1)
    (hSup : positiveSupport q = 2) :
    unitSupport q = 1 ∧ nonUnitPositiveSupport q = 1 := by
  have hbound :=
    (exponent_one_support_two_exact_mass q hEx hSup).2
  have heq :=
    floorExcess_eq_nonUnitPositiveSupport_of_le_two q hbound
  have hpart := positiveSupport_eq_unit_add_nonUnit q
  omega

/-- Direct concrete-centre interface used by the n=3 five-centre
no-top exceptional branch. -/
theorem next_saturated_support_two_has_exact_two_one_units
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t : ℝ}
    (hsat : nextSaturatedSupportTwo C t) :
    unitSupport (centreQuotient C t) = 1 ∧
      nonUnitPositiveSupport (centreQuotient C t) = 1 := by
  have hfloor :
      floorExcess (centreQuotient C t) = 1 := by
    have hmass := hsat.2.1
    have hsum := floorExcess_add_positiveSupport
      (centreQuotient C t)
    omega
  exact unit_and_double_counts_of_excess_one_support_two
    (centreQuotient C t) hfloor hsat.1

#print axioms floorExcess_eq_nonUnitPositiveSupport_of_le_two
#print axioms unit_and_double_counts_of_excess_one_support_two
#print axioms next_saturated_support_two_has_exact_two_one_units

end JSP000404Research
