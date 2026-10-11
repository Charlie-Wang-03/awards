import JSP000404Research.PlanarLowerBranchGlobalPaymentReplacement
import JSP000404Research.ResidualSaturatedHardRemainder
import Mathlib.Tactic

/-!
# Planar lower-branch dyadic capacity from SOFT + SATURATED-HARD payment

The lower-branch global payment is EXACTLY equivalent to paying
SOFT overlaps and remaining HARD overlaps after reserving the
full faces of ALL surplus-payable hard residual carriers.

This module has NO sorry and makes NO additional geometric claim:
the local and global rigid payment deductions are independently
kernel-verified for every ordered colouring. The STILL UNPROVED
planar input is now only

  softOverlapWords + unpaidHardOverlapWords + profileLoss
    <= BooleanHoles + (totalSurplus - paidRigidMass).

All fully surplus-paid hard words are removed from the overlap set,
and their exact full dyadic mass is deducted from global surplus.
No surplus can be double-charged by subsequently reusing the
gross total. The remaining payment contains SOFT overlaps, HARD overlaps with
at least one saturated endpoint under the usual residual-active
budget, and projected losses,
and remains equivalent to the original lower-branch capacity.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Reducing the unresolved lower-branch step to actual unpaid
SOFT plus unpaid-HARD words and NET surplus after certified reservations.
All arithmetic and transport reductions are admitted-free. -/
theorem planar_lower_branch_dyadic_capacity_of_soft_saturated_hard_remaining
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
        (unpaidHardOverlapWords B k).card +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (surplusPaidHardOverlapWords B k).card)) :
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
        (unpaidHardOverlapWords B k).card +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        (totalDyadicProfileSurplus k (projectedFree B) -
          (surplusPaidHardOverlapWords B k).card) := by
    exact hremaining
  have hpayment :=
    (completion_defect_payment_iff_soft_and_unpaid_hard
      B k).2 hremaining'
  exact exponent_capacity_of_completion_defect_payment B k hpayment

#print axioms planar_lower_branch_dyadic_capacity_of_soft_saturated_hard_remaining

end ProjectionOrdered
end JSP000404Research
