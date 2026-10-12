import JSP000404Research.PlanarLowerBranchBothMixedNetPaymentReduction
import Mathlib.Tactic

/-!
# ADMITTED RESEARCH-ONLY ENTRY: BOTH mixed-rigid net-payment frontier

One-layer geometry and exact global Boolean overlap accounting are
maintained. Whole-face payments on all previously certified payable
hard carriers are already reserved with no reused surplus.

The two remaining MIXED RIGID cases are now handled symmetrically:
  ascending: strict lower, saturated upper; reserve LOWER surplus;
  descending: saturated lower, strict upper; reserve UPPER surplus.

The complete overlap mass of each such pair is the chosen strict
endpoint surplus PLUS precisely ONE strict endpoint target weight.
Global hard-carrier matching makes all these reservations disjoint.

Exactly ONE executable sorry remains on genuine planar AngleCap data:
  softOverlapWords
    + hard words AFTER removing BOTH mixed rigid face families
    + SUM ascending lower target weights
    + SUM descending upper target weights
    + projected profile loss
  <= genuine Boolean holes
    + total surplus - whole-face hard reservations
                    - ascending lower-surplus credit
                    - descending upper-surplus credit.

Under the standard one-layer residual-active budget, every remaining
RIGID hard-overlap carrier is DOUBLY projected-saturated. Other hard
carriers may have an outward/inactive transport, but translated words
are still covered unless independent hole geometry is provided.

This net inequality remains EXACTLY EQUIVALENT to the unproved planar
lower-branch capacity. The admitted WIP has sorryAx and is NOT a
complete JSP-000404 proof or prize-submission certificate.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- ADMITTED. The residual planar payment goal is stated AFTER
collision-free whole-face hard payment and BOTH orientations of
globally disjoint mixed-rigid partial surplus payment.
The remaining goal stays equivalent to the original lower branch. -/
theorem planar_lower_branch_dyadic_capacity_admitted_wip
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
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  exact planar_lower_branch_dyadic_capacity_of_both_mixed_rigid_net_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- SOLE OPEN GEOMETRIC INPUT: true Boolean holes and net surplus
      -- must cover soft overlap + transportable/doubly-saturated
      -- hard overlap + BOTH mixed-rigid target weight debts + loss.
      -- All previous global face/partial-credit reservations are
      -- independently kernel-checked and are deducted exactly once.
      -- This remaining inequality is equivalent to the original
      -- lower-branch capacity; no geometric payment is assumed proved.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
