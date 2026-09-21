import JSP000404Research.BoundaryFreeProfile
import Mathlib.Tactic

/-!
# General boundary support exchange: lost positives create surplus

BoundaryFreeProfile used the hypothesis that every q-positive gap remains
b-positive.  That hypothesis is automatic at a genuine budget failure, but it
is unnecessarily restrictive for potential surplus centres.

Define

  lostPositiveSupport(q,b)
    = #{i | q(i)>0 and b(i)=0},

and recall

  zeroHitSupport(q,b)
    = #{i | q(i)=0 and b(i)>0}.

For arbitrary q,b there is an exact support exchange identity

  positiveSupport(b) + lostPositiveSupport(q,b)
    = positiveSupport(q) + zeroHitSupport(q,b).

If sum b=n and sum q<=n, writing

  k = floorExcess(q),
  d = n-sum q,
  nu = n-positiveSupport(b)=floorExcess(b),

this becomes the unconditional free-profile balance

  nu + zeroHitSupport(q,b)
    = k + d + lostPositiveSupport(q,b).

Thus losing a positive q-gap from the boundary support is not merely harmless:
it contributes one full extra free coordinate.  At genuine bad centres the
earlier theorem proves lostPositiveSupport=0; at good centres it is an
additional source of surplus which the bad-mass analysis discarded.
-/

namespace JSP000404Research

open scoped BigOperators

def lostPositiveSupport
    {I : Type*} [Fintype I]
    (q b : I → ℕ) : ℕ :=
  ∑ i, if q i ≠ 0 ∧ b i = 0 then 1 else 0

theorem positiveSupport_add_lost_eq_add_zeroHit
    {I : Type*} [Fintype I]
    (q b : I → ℕ) :
    positiveSupport b + lostPositiveSupport q b =
      positiveSupport q + zeroHitSupport q b := by
  classical
  unfold positiveSupport lostPositiveSupport zeroHitSupport
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hq : q i = 0 <;>
    by_cases hb : b i = 0 <;>
    simp [hq, hb]

theorem general_boundary_free_profile_balance
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n) :
    (n - positiveSupport b) + zeroHitSupport q b =
      floorExcess q + (n - ∑ i, q i) +
        lostPositiveSupport q b := by
  have hbID := floorExcess_add_positiveSupport b
  have hqID := floorExcess_add_positiveSupport q
  have hsupport :=
    positiveSupport_add_lost_eq_add_zeroHit q b
  rw [hsumB] at hbID
  have hqsum :
      floorExcess q + positiveSupport q =
        ∑ i, q i := hqID
  have hfree :
      n - positiveSupport b = floorExcess b := by
    omega
  rw [hfree]
  omega

/-- The earlier preserved-positive balance is recovered by setting the lost
positive support to zero. -/
theorem general_balance_of_no_lost_positive
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hnoLost : lostPositiveSupport q b = 0) :
    (n - positiveSupport b) + zeroHitSupport q b =
      floorExcess q + (n - ∑ i, q i) := by
  have h :=
    general_boundary_free_profile_balance q b n hsumB hQ
  rw [hnoLost, add_zero] at h
  exact h

/-- One surplus free coordinate is guaranteed whenever the combined unused
floor defect plus lost-positive support exceeds the zero-hit count. -/
theorem exponent_add_one_le_free_of_zeroHits_lt_defect_add_lost
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n)
    (hplus :
      zeroHitSupport q b <
        (n - ∑ i, q i) + lostPositiveSupport q b) :
    floorExcess q + 1 ≤ n - positiveSupport b := by
  have hbal :=
    general_boundary_free_profile_balance q b n hsumB hQ
  omega

/-- Exact one-layer loss is equivalent to zero-hit support exceeding the
combined defect-plus-lost-positive budget by one. -/
theorem free_add_one_eq_exponent_iff_zeroHits_eq_succ_defect_add_lost
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (n : ℕ)
    (hsumB : (∑ i, b i) = n)
    (hQ : (∑ i, q i) ≤ n) :
    (n - positiveSupport b) + 1 = floorExcess q ↔
      zeroHitSupport q b =
        (n - ∑ i, q i) + lostPositiveSupport q b + 1 := by
  have hbal :=
    general_boundary_free_profile_balance q b n hsumB hQ
  constructor <;> intro h <;> omega

/-- At a genuine budget failure no positive q-gap is lost, so the extra
surplus term vanishes. -/
theorem lostPositiveSupport_eq_zero_of_budget_failure
    {I : Type*} [Fintype I]
    (q b : I → ℕ) (e : I) (n : ℕ)
    (hsum : (∑ i, b i) = n)
    (hregular : ∀ i, i ≠ e → q i ≤ b i)
    (hexception : q e ≤ b e + 1)
    (hbad : n - floorExcess q < positiveSupport b) :
    lostPositiveSupport q b = 0 := by
  have hpres :=
    positive_gap_preserved_of_budget_failure
      q b e n hsum hregular hexception hbad
  unfold lostPositiveSupport
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hqi : q i = 0
  · simp [hqi]
  · have hbi : b i ≠ 0 := hpres i hqi
    simp [hqi, hbi]

#print axioms positiveSupport_add_lost_eq_add_zeroHit
#print axioms general_boundary_free_profile_balance
#print axioms exponent_add_one_le_free_of_zeroHits_lt_defect_add_lost
#print axioms free_add_one_eq_exponent_iff_zeroHits_eq_succ_defect_add_lost
#print axioms lostPositiveSupport_eq_zero_of_budget_failure

end JSP000404Research
