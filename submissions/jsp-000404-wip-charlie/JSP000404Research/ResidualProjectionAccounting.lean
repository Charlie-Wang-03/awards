
import JSP000404Research.WeightedProfileRepair
import Mathlib.Tactic

/-!
# Master accounting for residual projection

Let nu(v) be the free-coordinate profile after projecting an (n+1)-colour
certificate to n retained coordinates.

Suppose the total projected completion mass admits the exact decomposition

  sum_v 2^nu(v) = unionMass + overlapMass,

where unionMass is the number of retained Boolean words covered at least once
and overlapMass is the extra multiplicity beyond the first cover.

WeightedProfileRepair gives the independent exact balance

  targetMass + profileSurplus
    = projectedMass + profileLoss.

Combining the two identities yields

  targetMass + profileSurplus
    = unionMass + overlapMass + profileLoss.

Since the ambient retained cube has 2^n words, write

  holeMass = 2^n - unionMass.

Then the sharp n-bit capacity is equivalent to the single defect inequality

  overlapMass + profileLoss
    <= holeMass + profileSurplus.

This is the natural global residual-colour accounting.  It treats projected
cube overlaps and one-layer profile losses as costs, while genuine Boolean
holes and profile surplus are the two available credits.
-/

namespace JSP000404Research

open scoped BigOperators

theorem residual_projection_accounting_balance
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (unionMass overlapMass : ℕ)
    (hproject :
      (∑ v, 2 ^ nu v) =
        unionMass + overlapMass) :
    (∑ v, 2 ^ k v) +
        totalDyadicProfileSurplus k nu =
      unionMass + overlapMass +
        totalDyadicProfileLoss k nu := by
  have hbal := dyadic_profile_total_balance k nu
  rw [hproject] at hbal
  omega

/-- Defect payment implies the sharp ambient n-bit capacity. -/
theorem dyadic_capacity_of_residual_projection_accounting
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (n unionMass overlapMass : ℕ)
    (hunion : unionMass ≤ 2 ^ n)
    (hproject :
      (∑ v, 2 ^ nu v) =
        unionMass + overlapMass)
    (hpay :
      overlapMass +
          totalDyadicProfileLoss k nu
        ≤
      (2 ^ n - unionMass) +
          totalDyadicProfileSurplus k nu) :
    (∑ v, 2 ^ k v) ≤ 2 ^ n := by
  have hbal :=
    residual_projection_accounting_balance
      k nu unionMass overlapMass hproject
  omega

/-- Conversely, once the projected-mass decomposition is exact, the sharp
capacity inequality itself forces exactly the same global defect payment. -/
theorem residual_projection_accounting_of_dyadic_capacity
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (n unionMass overlapMass : ℕ)
    (hunion : unionMass ≤ 2 ^ n)
    (hproject :
      (∑ v, 2 ^ nu v) =
        unionMass + overlapMass)
    (hcap :
      (∑ v, 2 ^ k v) ≤ 2 ^ n) :
    overlapMass +
        totalDyadicProfileLoss k nu
      ≤
    (2 ^ n - unionMass) +
        totalDyadicProfileSurplus k nu := by
  have hbal :=
    residual_projection_accounting_balance
      k nu unionMass overlapMass hproject
  omega

/-- Exact equivalence form. -/
theorem residual_projection_accounting_iff
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (n unionMass overlapMass : ℕ)
    (hunion : unionMass ≤ 2 ^ n)
    (hproject :
      (∑ v, 2 ^ nu v) =
        unionMass + overlapMass) :
    ((∑ v, 2 ^ k v) ≤ 2 ^ n)
      ↔
    (overlapMass +
          totalDyadicProfileLoss k nu
        ≤
      (2 ^ n - unionMass) +
          totalDyadicProfileSurplus k nu) := by
  constructor
  · exact residual_projection_accounting_of_dyadic_capacity
      k nu n unionMass overlapMass hunion hproject
  · exact dyadic_capacity_of_residual_projection_accounting
      k nu n unionMass overlapMass hunion hproject

#print axioms residual_projection_accounting_balance
#print axioms dyadic_capacity_of_residual_projection_accounting
#print axioms residual_projection_accounting_of_dyadic_capacity
#print axioms residual_projection_accounting_iff

end JSP000404Research
