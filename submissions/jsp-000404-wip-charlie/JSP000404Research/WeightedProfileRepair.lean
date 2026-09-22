import JSP000404Research.TailMajorizationCapacity
import Mathlib.Tactic

/-!
# Global weighted repair between two dyadic profiles

Threshold-by-threshold tail domination is sufficient for the Sendov dyadic
capacity, but it is stronger than necessary and implicitly favours comb-like
profiles.

For arbitrary natural-valued profiles k and nu define the pointwise dyadic
loss and surplus

  loss(v)    = 2^k(v)  - 2^nu(v),
  surplus(v) = 2^nu(v) - 2^k(v),

where subtraction is truncated in Nat.

The elementary identity

  2^k + surplus = 2^nu + loss

holds pointwise.  Hence after summing over a finite vertex set,

  targetMass + surplusMass
    = certificateMass + lossMass.

Therefore the single aggregate condition

  lossMass <= surplusMass

already implies

  sum_v 2^k(v) <= sum_v 2^nu(v).

No threshold matching, ordering of exponents, or comb-profile hypothesis is
needed.  If nu is the free-coordinate profile of an n-colour Hansel/adaptive
certificate, this immediately yields the sharp 2^n Sendov capacity.

This is the weakest purely profile-level repair outlet currently used by the
project.
-/

namespace JSP000404Research

open scoped BigOperators

def dyadicProfileLoss
    {V : Type*}
    (k nu : V → ℕ) (v : V) : ℕ :=
  2 ^ k v - 2 ^ nu v

def dyadicProfileSurplus
    {V : Type*}
    (k nu : V → ℕ) (v : V) : ℕ :=
  2 ^ nu v - 2 ^ k v

def totalDyadicProfileLoss
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) : ℕ :=
  ∑ v, dyadicProfileLoss k nu v

def totalDyadicProfileSurplus
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) : ℕ :=
  ∑ v, dyadicProfileSurplus k nu v

theorem dyadic_loss_surplus_pointwise_balance
    {a b : ℕ} :
    a + (b - a) = b + (a - b) := by
  omega

theorem dyadic_profile_pointwise_balance
    {V : Type*}
    (k nu : V → ℕ) (v : V) :
    2 ^ k v + dyadicProfileSurplus k nu v =
      2 ^ nu v + dyadicProfileLoss k nu v := by
  unfold dyadicProfileLoss dyadicProfileSurplus
  exact dyadic_loss_surplus_pointwise_balance

theorem dyadic_profile_total_balance
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) :
    (∑ v, 2 ^ k v) + totalDyadicProfileSurplus k nu =
      (∑ v, 2 ^ nu v) + totalDyadicProfileLoss k nu := by
  unfold totalDyadicProfileLoss totalDyadicProfileSurplus
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  exact dyadic_profile_pointwise_balance k nu v

/-- Aggregate weighted loss paid by aggregate weighted surplus is exactly the
profile comparison needed for the final dyadic mass. -/
theorem dyadic_sum_le_of_total_loss_le_surplus
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (hrepair :
      totalDyadicProfileLoss k nu ≤
        totalDyadicProfileSurplus k nu) :
    (∑ v, 2 ^ k v) ≤ ∑ v, 2 ^ nu v := by
  have hbal := dyadic_profile_total_balance k nu
  omega

/-- Any external capacity bound on the comparison profile nu can therefore be
used after one aggregate weighted repair inequality. -/
theorem dyadic_capacity_of_total_loss_le_surplus
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (bound : ℕ)
    (hrepair :
      totalDyadicProfileLoss k nu ≤
        totalDyadicProfileSurplus k nu)
    (hcap :
      (∑ v, 2 ^ nu v) ≤ bound) :
    (∑ v, 2 ^ k v) ≤ bound :=
  (dyadic_sum_le_of_total_loss_le_surplus
    k nu hrepair).trans hcap

/-- Tail domination implies aggregate weighted repair, confirming that this
criterion is no stronger than the earlier layer-cake outlet. -/
theorem total_loss_le_surplus_of_dyadic_sum_le
    {V : Type*} [Fintype V]
    (k nu : V → ℕ)
    (h :
      (∑ v, 2 ^ k v) ≤ ∑ v, 2 ^ nu v) :
    totalDyadicProfileLoss k nu ≤
      totalDyadicProfileSurplus k nu := by
  have hbal := dyadic_profile_total_balance k nu
  omega

theorem total_loss_le_surplus_of_tailCount_le
    {V : Type*} [Fintype V]
    (k nu : V → ℕ) (n : ℕ)
    (hk : ∀ v, k v ≤ n)
    (hnu : ∀ v, nu v ≤ n)
    (htail :
      ∀ r < n, tailCount k r ≤ tailCount nu r) :
    totalDyadicProfileLoss k nu ≤
      totalDyadicProfileSurplus k nu := by
  apply total_loss_le_surplus_of_dyadic_sum_le
  exact dyadic_sum_le_of_tailCount_le
    k nu n hk hnu htail

/-- One-layer loss has an exact dyadic price: if k=nu+1 then the missing mass
is exactly 2^nu. -/
theorem dyadicProfileLoss_eq_of_exact_one_loss
    {V : Type*}
    (k nu : V → ℕ) (v : V)
    (h : k v = nu v + 1) :
    dyadicProfileLoss k nu v = 2 ^ nu v := by
  unfold dyadicProfileLoss
  rw [h, pow_succ]
  omega

/-- One full surplus layer supplies at least one copy of the target weight. -/
theorem target_weight_le_dyadicProfileSurplus_of_one_surplus
    {V : Type*}
    (k nu : V → ℕ) (v : V)
    (h : k v + 1 ≤ nu v) :
    2 ^ k v ≤ dyadicProfileSurplus k nu v := by
  unfold dyadicProfileSurplus
  have hp :
      2 ^ (k v + 1) ≤ 2 ^ nu v :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) h
  rw [pow_succ] at hp
  omega

#print axioms dyadic_profile_total_balance
#print axioms dyadic_sum_le_of_total_loss_le_surplus
#print axioms dyadic_capacity_of_total_loss_le_surplus
#print axioms total_loss_le_surplus_of_tailCount_le
#print axioms dyadicProfileLoss_eq_of_exact_one_loss
#print axioms target_weight_le_dyadicProfileSurplus_of_one_surplus

end JSP000404Research
