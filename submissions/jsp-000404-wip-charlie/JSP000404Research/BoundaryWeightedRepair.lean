import JSP000404Research.BoundaryFreeProfile
import JSP000404Research.WeightedProfileRepair
import Mathlib.Tactic

/-!
# Weighted repair from the exact zero-hit balance

For one phase of the one-long-spacing construction, BoundaryFreeProfile gives
at every centre the exact conservation law

  nu + z = k + d,

where

* k  is the Sendov floor-excess exponent,
* nu is the number of free phase coordinates,
* d  is the floor defect n - sum q,
* z  is the number of zero-quotient gaps hit by phase boundaries.

The geometry also gives the one-layer bound z <= d+1.

The conservation law immediately identifies the two weighted events:

  k = nu+1    iff    z = d+1,
  k+1 <= nu   iff    z < d.

Thus exact one-layer loss is precisely one extra zero hit, while every omitted
zero hit creates at least one full surplus layer.

This module rewrites WeightedProfileRepair entirely in terms of the zero-hit
statistics.  No sorted exponent profile, threshold matching, or comb
extremizer is needed.
-/

namespace JSP000404Research

open scoped BigOperators

def zeroHitLossWeight
    {V : Type*} [Fintype V]
    (nu d z : V → ℕ) : ℕ :=
  ∑ v, if z v = d v + 1 then 2 ^ nu v else 0

def zeroHitSurplusCredit
    {V : Type*} [Fintype V]
    (k d z : V → ℕ) : ℕ :=
  ∑ v, if z v < d v then 2 ^ k v else 0

/-- Exact one-layer loss is equivalent to one zero hit beyond the floor
defect.  Only the conservation law is needed. -/
theorem exact_one_loss_iff_zeroHit_succ
    {k nu d z : ℕ}
    (hbal : nu + z = k + d) :
    k = nu + 1 ↔ z = d + 1 := by
  omega

/-- One full surplus layer is equivalent to leaving at least one floor-defect
unit unused by zero hits. -/
theorem one_surplus_iff_zeroHit_lt
    {k nu d z : ℕ}
    (hbal : nu + z = k + d) :
    k + 1 ≤ nu ↔ z < d := by
  omega

/-- The geometric upper bound z<=d+1 is exactly what is needed to ensure that
the phase can lose at most one free coordinate. -/
theorem exponent_le_free_add_one_of_zeroHit_le_succ
    {k nu d z : ℕ}
    (hbal : nu + z = k + d)
    (hz : z ≤ d + 1) :
    k ≤ nu + 1 := by
  omega

/-- If zero hits do not exceed the floor defect, there is no profile loss. -/
theorem exponent_le_free_of_zeroHit_le
    {k nu d z : ℕ}
    (hbal : nu + z = k + d)
    (hz : z ≤ d) :
    k ≤ nu := by
  omega

/-- If z<=d, the surplus depth is exactly d-z. -/
theorem free_eq_exponent_add_unused_defect
    {k nu d z : ℕ}
    (hbal : nu + z = k + d)
    (hz : z ≤ d) :
    nu = k + (d - z) := by
  omega

/-- Under exact balance, the old one-layer loss weight is literally the
zero-hit loss weight. -/
theorem oneLayerLossWeight_eq_zeroHitLossWeight
    {V : Type*} [Fintype V]
    (k nu d z : V → ℕ)
    (hbal : ∀ v, nu v + z v = k v + d v) :
    oneLayerLossWeight k nu =
      zeroHitLossWeight nu d z := by
  unfold oneLayerLossWeight zeroHitLossWeight
  apply Finset.sum_congr rfl
  intro v _
  have hiff :=
    exact_one_loss_iff_zeroHit_succ
      (hbal v)
  by_cases h : k v = nu v + 1
  · have hz : z v = d v + 1 := hiff.mp h
    simp [h, hz]
  · have hz : z v ≠ d v + 1 := by
      intro hz
      exact h (hiff.mpr hz)
    simp [h, hz]

/-- Under exact balance, the standard one-layer surplus credit is literally
the credit from centres with z<d. -/
theorem oneLayerSurplusCredit_eq_zeroHitSurplusCredit
    {V : Type*} [Fintype V]
    (k nu d z : V → ℕ)
    (hbal : ∀ v, nu v + z v = k v + d v) :
    oneLayerSurplusCredit k nu =
      zeroHitSurplusCredit k d z := by
  unfold oneLayerSurplusCredit zeroHitSurplusCredit
  apply Finset.sum_congr rfl
  intro v _
  have hiff :=
    one_surplus_iff_zeroHit_lt
      (hbal v)
  by_cases h : k v + 1 ≤ nu v
  · have hz : z v < d v := hiff.mp h
    simp [h, hz]
  · have hz : ¬ z v < d v := by
      intro hz
      exact h (hiff.mpr hz)
    simp [h, hz]

/-- Exact balance plus z<=d+1 gives the global one-layer profile bound. -/
theorem profile_oneLayer_of_zeroHit_balance
    {V : Type*}
    (k nu d z : V → ℕ)
    (hbal : ∀ v, nu v + z v = k v + d v)
    (hz : ∀ v, z v ≤ d v + 1) :
    ∀ v, k v ≤ nu v + 1 := by
  intro v
  exact exponent_le_free_add_one_of_zeroHit_le_succ
    (hbal v) (hz v)

/-- Main zero-hit weighted-repair theorem.

To compare the target exponent profile k with the phase free profile nu, it is
enough that the dyadic weight of centres with one extra zero hit be paid by
the target-weight credit of centres that leave at least one floor-defect unit
unused. -/
theorem dyadic_sum_le_of_zeroHit_weighted_repair
    {V : Type*} [Fintype V]
    (k nu d z : V → ℕ)
    (hbal : ∀ v, nu v + z v = k v + d v)
    (hz : ∀ v, z v ≤ d v + 1)
    (hrepair :
      zeroHitLossWeight nu d z ≤
        zeroHitSurplusCredit k d z) :
    (∑ v, 2 ^ k v) ≤ ∑ v, 2 ^ nu v := by
  have hone :
      ∀ v, k v ≤ nu v + 1 :=
    profile_oneLayer_of_zeroHit_balance
      k nu d z hbal hz
  apply dyadic_sum_le_of_oneLayer_weighted_repair
    k nu hone
  rw [oneLayerLossWeight_eq_zeroHitLossWeight
        k nu d z hbal,
      oneLayerSurplusCredit_eq_zeroHitSurplusCredit
        k nu d z hbal]
  exact hrepair

/-- Capacity form against any external n-bit certificate. -/
theorem dyadic_capacity_of_zeroHit_weighted_repair
    {V : Type*} [Fintype V]
    (k nu d z : V → ℕ)
    (bound : ℕ)
    (hbal : ∀ v, nu v + z v = k v + d v)
    (hz : ∀ v, z v ≤ d v + 1)
    (hrepair :
      zeroHitLossWeight nu d z ≤
        zeroHitSurplusCredit k d z)
    (hcap : (∑ v, 2 ^ nu v) ≤ bound) :
    (∑ v, 2 ^ k v) ≤ bound :=
  (dyadic_sum_le_of_zeroHit_weighted_repair
    k nu d z hbal hz hrepair).trans hcap

/-- Concrete one-centre specialization of the exact conservation law from
BoundaryFreeProfile. -/
theorem concrete_boundary_zeroHit_balance
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0) :
    (n - positiveSupport b) + zeroHitSupport q b =
      floorExcess q + (n - ∑ i, q i) :=
  boundary_free_profile_balance
    q b n hsumB hQ hpres

#print axioms exact_one_loss_iff_zeroHit_succ
#print axioms one_surplus_iff_zeroHit_lt
#print axioms free_eq_exponent_add_unused_defect
#print axioms oneLayerLossWeight_eq_zeroHitLossWeight
#print axioms oneLayerSurplusCredit_eq_zeroHitSurplusCredit
#print axioms dyadic_sum_le_of_zeroHit_weighted_repair
#print axioms dyadic_capacity_of_zeroHit_weighted_repair

end JSP000404Research
