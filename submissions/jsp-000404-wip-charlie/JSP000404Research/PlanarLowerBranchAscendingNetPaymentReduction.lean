import JSP000404Research.PlanarLowerBranchSaturatedHardReduction
import JSP000404Research.ResidualUnpaidRigidNetPaymentReduction
import Mathlib.Tactic

/-!
# Planar lower-branch interface after exact ascending-rigid partial payment

This is a sorry-free bridge from the further reduced TRUE geometric debt:
  soft overlaps + all nonascending unpaid hard Boolean words
  + ascending rigid LOWER TARGET MASS + projected profile loss
    <= Boolean holes + original surplus NET of full and partial charges.

The new exact net payment equivalence is kernel-certified separately.
No claim that planar AngleCap implies this inequality is made here.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Reducing the unresolved lower-branch step to actual unpaid
SOFT plus unpaid-HARD words and NET surplus after certified reservations.
All arithmetic and transport reductions are admitted-free. -/
theorem planar_lower_branch_dyadic_capacity_of_net_ascending_rigid_remaining
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hremaining :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t := by
        rw [ht]
        have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let B := standardResidualColoring D n (by exact_mod_cast hwidth)
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      (softOverlapCompletionWords B).card +
        (unpaidHardOverlapWords B k \
          ascendingUnpaidRigidWords B k).card +
        (∑ q ∈ ascendingUnpaidRigidCarriers B k, 2 ^ k q.1) +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (surplusPaidHardOverlapWords B k).card -
          (∑ q ∈ ascendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.1))) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change (∑ i : ProjectionOrdered V, 2 ^ k i) ≤ 2 ^ n
  have hremaining' :
      (softOverlapCompletionWords B).card +
        (unpaidHardOverlapWords B k \
          ascendingUnpaidRigidWords B k).card +
        (∑ q ∈ ascendingUnpaidRigidCarriers B k, 2 ^ k q.1) +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (surplusPaidHardOverlapWords B k).card -
          (∑ q ∈ ascendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.1)) := by
    exact hremaining
  have hpayment :=
    (completion_defect_payment_iff_after_ascending_partial_credit
      B k).2 hremaining'
  exact planar_lower_branch_dyadic_capacity_of_soft_saturated_hard_remaining
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hpayment

#print axioms planar_lower_branch_dyadic_capacity_of_net_ascending_rigid_remaining

end ProjectionOrdered
end JSP000404Research
