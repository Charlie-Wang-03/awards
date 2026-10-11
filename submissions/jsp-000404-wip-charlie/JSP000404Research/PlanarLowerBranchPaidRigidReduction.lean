import JSP000404Research.PlanarLowerBranchGlobalPaymentReplacement
import JSP000404Research.ResidualRigidPaidDefectReduction
import Mathlib.Tactic

/-!
# Planar lower-branch dyadic capacity from reduced RIGID-PAID payment

The lower-branch global payment is EXACTLY equivalent to a strictly
more focused payment statement after reserving the whole Boolean
faces of one-sided-surplus-paid nested rigid hard overlaps.

This module has NO sorry and makes NO additional geometric claim:
the local and global rigid payment deductions are independently
kernel-verified for every ordered colouring. The STILL UNPROVED
planar input is now only

  remainingOverlapWords + profileLoss
    <= BooleanHoles + (totalSurplus - paidRigidMass).

The paid rigid words are physically removed from the overlap set,
and their exact full dyadic mass is deducted from global surplus.
No surplus can be double-charged by subsequently reusing the
gross total. The remaining payment still contains transportable
hard overlaps, unpaid rigid overlaps, soft overlaps, and loss,
and remains equivalent to the original lower-branch capacity.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Reducing the unresolved lower-branch step to actual unpaid
completion words and NET surplus after certified rigid reservations.
All arithmetic and transport reductions are admitted-free. -/
theorem planar_lower_branch_dyadic_capacity_of_paid_rigid_remaining
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
      (afterRigidPaymentOverlapWords B k).card +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (oneSidedPaidRigidOverlapWords B k).card)) :
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
      (afterRigidPaymentOverlapWords B k).card +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (oneSidedPaidRigidOverlapWords B k).card) := by
    exact hremaining
  have hpayment :=
    (completion_defect_payment_iff_after_oneSided_rigid_reservation
      B k).2 hremaining'
  exact exponent_capacity_of_completion_defect_payment B k hpayment

#print axioms planar_lower_branch_dyadic_capacity_of_paid_rigid_remaining

end ProjectionOrdered
end JSP000404Research
