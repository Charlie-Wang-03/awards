import JSP000404Research.PlanarLowerBranchSaturatedHardReduction
import JSP000404Research.ResidualBothMixedRigidNetReduction
import JSP000404Research.ResidualTerminalDoubleSaturatedHard
import Mathlib.Tactic

/-!
# Planar lower branch conditional bridge after BOTH mixed-rigid credits

This is a sorry-free link from the new exact global net debt
to the original lower-branch dyadic capacity. The net debt
contains the SOFT overlaps, the still-unpaid transportable or
double-saturated rigid hard words, both strict-endpoint
target-weight debts, and projected profile losses; on the
payment side only TRUE Boolean holes and genuinely UNRESERVED
dyadic surplus remain.

The net debt is still equivalent to the original lower-branch
capacity. This module deliberately does NOT prove that the
planar AngleCap conditions imply the remaining inequality.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Kernel-checked reduction from the narrower mixed-rigid
net-payment obligation to the genuine planar dyadic bound. -/
theorem planar_lower_branch_dyadic_capacity_of_both_mixed_rigid_net_payment
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
        (remainingUnpaidHardAfterMixedRigidWords B k).card +
        (∑ q ∈ ascendingUnpaidRigidCarriers B k, 2 ^ k q.1) +
        (∑ q ∈ descendingUnpaidRigidCarriers B k, 2 ^ k q.2) +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (surplusPaidHardOverlapWords B k).card -
          (∑ q ∈ ascendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.1) -
          (∑ q ∈ descendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.2))) :
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
        (remainingUnpaidHardAfterMixedRigidWords B k).card +
        (∑ q ∈ ascendingUnpaidRigidCarriers B k, 2 ^ k q.1) +
        (∑ q ∈ descendingUnpaidRigidCarriers B k, 2 ^ k q.2) +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (surplusPaidHardOverlapWords B k).card -
          (∑ q ∈ ascendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.1) -
          (∑ q ∈ descendingUnpaidRigidCarriers B k,
            dyadicProfileSurplus k (projectedFree B) q.2)) := by
    exact hremaining
  have hpayment :=
    (completion_defect_payment_iff_after_both_mixed_rigid_credits
      B k).2 hremaining'
  exact planar_lower_branch_dyadic_capacity_of_soft_saturated_hard_remaining
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles hpayment

#print axioms planar_lower_branch_dyadic_capacity_of_both_mixed_rigid_net_payment

end ProjectionOrdered
end JSP000404Research
