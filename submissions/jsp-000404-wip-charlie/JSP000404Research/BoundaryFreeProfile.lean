import JSP000404Research.BoundaryExcessBalance
import JSP000404Research.BoundaryFailureStructure
import Mathlib.Tactic

/-!
# Exact free-profile balance for a one-long-spacing phase

Let q be the fixed geometric quotient profile at one centre and b the
boundary-count profile produced by one phase of an n-colour one-long-spacing
partition.

Because sum b = n, the number of free colours at the centre is exactly

  n - positiveSupport(b) = floorExcess(b).

Write

  k = floorExcess(q),
  d = n - sum q,
  z = zeroHitSupport(q,b).

Whenever all q-positive gaps remain b-positive, BoundaryExcessBalance gives

  floorExcess(b) + z = k + d.

Thus the phase free profile differs from the Sendov exponent by the exact
zero-gap balance d-z:

* z=d+1  <=> one exact free-coordinate loss;
* z=d    <=> exact match;
* z<d    <=> at least one surplus free coordinate.

This is the profile-level conservation law needed by TailMajorizationCapacity.
It records both losses and compensating surplus, unlike the earlier bad-mass
route which retained only the loss events.
-/

namespace JSP000404Research

open scoped BigOperators

theorem freeCount_eq_floorExcess_of_boundary_sum
    {I : Type*} [Fintype I]
    (b : I → ℕ) (n : ℕ)
    (hsum : (∑ i, b i) = n) :
    n - positiveSupport b = floorExcess b := by
  have hid := floorExcess_add_positiveSupport b
  rw [hsum] at hid
  omega

theorem boundary_free_profile_balance
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0) :
    (n - positiveSupport b) + zeroHitSupport q b =
      floorExcess q + (n - ∑ i, q i) := by
  rw [freeCount_eq_floorExcess_of_boundary_sum b n hsumB]
  exact boundary_excess_add_zeroHits_eq
    q b n hsumB hQ hpres

/-- Exact one-layer loss iff the zero-hit count exceeds the floor defect by
exactly one. -/
theorem boundary_free_add_one_eq_exponent_iff_zeroHits_eq_succ
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0) :
    (n - positiveSupport b) + 1 = floorExcess q ↔
      zeroHitSupport q b = (n - ∑ i, q i) + 1 := by
  have hbal :=
    boundary_free_profile_balance q b n hsumB hQ hpres
  constructor <;> intro h <;> omega

/-- Exact profile match iff zero hits equal the floor defect. -/
theorem boundary_free_eq_exponent_iff_zeroHits_eq_floorDefect
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0) :
    n - positiveSupport b = floorExcess q ↔
      zeroHitSupport q b = n - ∑ i, q i := by
  have hbal :=
    boundary_free_profile_balance q b n hsumB hQ hpres
  constructor <;> intro h <;> omega

/-- At least one surplus free coordinate iff at least one unit of floor defect
is left unused by zero-gap hits. -/
theorem exponent_add_one_le_boundary_free_iff_zeroHits_lt_floorDefect
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hpres : ∀ i, q i ≠ 0 → b i ≠ 0) :
    floorExcess q + 1 ≤ n - positiveSupport b ↔
      zeroHitSupport q b < n - ∑ i, q i := by
  have hbal :=
    boundary_free_profile_balance q b n hsumB hQ hpres
  constructor <;> intro h <;> omega

/-- One-exception domination implies that the phase free count can fall at
most one below the Sendov exponent. -/
theorem exponent_le_boundary_free_add_one_of_one_exception
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1) :
    floorExcess q ≤ (n - positiveSupport b) + 1 := by
  have hloss :=
    floorExcess_le_add_one_of_one_exception
      q b e hregular hexception
  rw [freeCount_eq_floorExcess_of_boundary_sum b n hsumB]
  exact hloss

#print axioms freeCount_eq_floorExcess_of_boundary_sum
#print axioms boundary_free_profile_balance
#print axioms boundary_free_add_one_eq_exponent_iff_zeroHits_eq_succ
#print axioms exponent_add_one_le_boundary_free_iff_zeroHits_lt_floorDefect
#print axioms exponent_le_boundary_free_add_one_of_one_exception

end JSP000404Research
