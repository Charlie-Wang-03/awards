import JSP000404Research.ZeroCarry
import Mathlib.Tactic

/-!
# Boundary-count reformulation of the local phase budget

Fix a centre and a rotating n-boundary phase partition.  Away from event
phases, each partition boundary lies in exactly one cyclic ray gap.

Let b i be the number of partition boundaries lying in ray gap i.  Then

  sum_i b i = n.

The number of active phase colours is the number of ray gaps which contain at
least one partition boundary, namely positiveSupport b.  (The geometric
duality between active cells and boundary-hit ray gaps is kept separate.)

For the Sendov quotient vector q, the desired local colour budget is

  active <= ell,     ell = n - floorExcess q.

Using the zero-carry identity for b,

  floorExcess b + positiveSupport b = n,

the budget is therefore equivalent to

  floorExcess q <= floorExcess b.

Thus a bad phase is exactly a phase at which the boundary-count vector loses
floor-excess relative to the geometric quotient vector.
-/

namespace JSP000404Research

open scoped BigOperators

/-- When a boundary-count vector has total mass n, its positive support is
exactly n minus its floor excess. -/
theorem positiveSupport_eq_total_sub_floorExcess
    {I : Type*} [Fintype I]
    (b : I → ℕ) (n : ℕ)
    (hsum : (∑ i, b i) = n) :
    positiveSupport b = n - floorExcess b := by
  have hid := floorExcess_add_positiveSupport b
  omega

/-- Exact arithmetic equivalence between the local active-colour budget and
comparison of floor-excess functionals.

In the geometric application, q is the scaled ray-gap quotient vector and b
counts phase-partition boundaries in the same ray gaps. -/
theorem support_budget_iff_floorExcess_le
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsum : (∑ i, b i) = n) :
    positiveSupport b ≤ n - floorExcess q ↔
      floorExcess q ≤ floorExcess b := by
  rw [positiveSupport_eq_total_sub_floorExcess b n hsum]
  have hb_le : floorExcess b ≤ n := by
    have hle := floorExcess_le_sum b
    rw [hsum] at hle
    exact hle
  constructor <;> intro h <;> omega

/-- Strict failure form: the local phase budget fails exactly when the
boundary-count floor excess is strictly smaller than the Sendov gap floor
excess. -/
theorem support_budget_fails_iff_floorExcess_lt
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsum : (∑ i, b i) = n) :
    n - floorExcess q < positiveSupport b ↔
      floorExcess b < floorExcess q := by
  rw [positiveSupport_eq_total_sub_floorExcess b n hsum]
  have hb_le : floorExcess b ≤ n := by
    have hle := floorExcess_le_sum b
    rw [hsum] at hle
    exact hle
  omega

/-- If the geometric side proves that the phase boundary allocation can lose
at most one unit of floor excess, then every local active count is at most
ell+1. -/
theorem support_le_deficit_add_one_of_excess_loss_le_one
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hloss : floorExcess q ≤ floorExcess b + 1) :
    positiveSupport b ≤ n - floorExcess q + 1 := by
  rw [positiveSupport_eq_total_sub_floorExcess b n hsum]
  have hb_le : floorExcess b ≤ n := by
    have hle := floorExcess_le_sum b
    rw [hsum] at hle
    exact hle
  omega

#print axioms positiveSupport_eq_total_sub_floorExcess
#print axioms support_budget_iff_floorExcess_le
#print axioms support_budget_fails_iff_floorExcess_lt
#print axioms support_le_deficit_add_one_of_excess_loss_le_one

end JSP000404Research
