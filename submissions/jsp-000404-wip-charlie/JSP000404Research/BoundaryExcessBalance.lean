import JSP000404Research.BoundaryFailureDistribution
import Mathlib.Tactic

/-!
# Exact excess balance through zero-gap hits

Let q be a geometric quotient vector and b a phase-boundary count vector with
total boundary mass n.  Assume every q-positive gap remains b-positive.

Write

  d = n - sum q
  z = zeroHitSupport q b.

Then the two zero-carry identities give the exact conservation law

  floorExcess b + z = floorExcess q + d.

Thus all variation of the phase floor excess is accounted for by the number of
q-zero gaps which receive a boundary.

Consequences:

* if z <= d, the phase meets the desired local budget;
* under one-exception domination, z can exceed d by at most one;
* the unique bad case is z = d+1, where the phase floor excess is exactly one
  below the geometric floor excess.

This is the arithmetic form best suited to a future weighted averaging or
charging argument.
-/

namespace JSP000404Research

open scoped BigOperators

theorem boundary_excess_add_zeroHits_eq
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0) :
    floorExcess b + zeroHitSupport q b =
      floorExcess q + (n - ∑ i, q i) := by
  have hbID := floorExcess_add_positiveSupport b
  have hqID := floorExcess_add_positiveSupport q
  have hsplit :=
    positiveSupport_eq_add_zeroHitSupport q b hpres
  rw [hsumB] at hbID
  omega

/-- Hitting at most d zero gaps is enough for the exact local budget. -/
theorem floorExcess_ge_of_zeroHits_le_floorDefect
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0)
    (hz : zeroHitSupport q b ≤ n - ∑ i, q i) :
    floorExcess q ≤ floorExcess b := by
  have hbal :=
    boundary_excess_add_zeroHits_eq q b n hsumB hQ hpres
  omega

/-- Hence the support/active-colour budget follows immediately. -/
theorem support_budget_of_zeroHits_le_floorDefect
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0)
    (hz : zeroHitSupport q b ≤ n - ∑ i, q i) :
    positiveSupport b ≤ n - floorExcess q := by
  exact (support_budget_iff_floorExcess_le q b n hsumB).2
    (floorExcess_ge_of_zeroHits_le_floorDefect
      q b n hsumB hQ hpres hz)

/-- If exactly d+1 zero gaps are hit, the phase floor excess is exactly one
below the geometric floor excess. -/
theorem floorExcess_add_one_eq_of_zeroHits_eq_succ_floorDefect
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0)
    (hz : zeroHitSupport q b = (n - ∑ i, q i) + 1) :
    floorExcess b + 1 = floorExcess q := by
  have hbal :=
    boundary_excess_add_zeroHits_eq q b n hsumB hQ hpres
  omega

/-- Under one-exception domination and positive-gap preservation, the zero-hit
count is at most d+1. -/
theorem zeroHits_le_succ_floorDefect_of_one_exception
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1) :
    zeroHitSupport q b ≤ (n - ∑ i, q i) + 1 := by
  have hbal :=
    boundary_excess_add_zeroHits_eq q b n hsumB hQ hpres
  have hloss :=
    floorExcess_le_add_one_of_one_exception
      q b e hregular hexception
  omega

#print axioms boundary_excess_add_zeroHits_eq
#print axioms floorExcess_ge_of_zeroHits_le_floorDefect
#print axioms support_budget_of_zeroHits_le_floorDefect
#print axioms floorExcess_add_one_eq_of_zeroHits_eq_succ_floorDefect
#print axioms zeroHits_le_succ_floorDefect_of_one_exception

end JSP000404Research
