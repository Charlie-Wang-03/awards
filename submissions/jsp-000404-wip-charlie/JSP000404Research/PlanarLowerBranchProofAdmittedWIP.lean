import JSP000404Research.PlanarLowerBranchPaidRigidReduction
import Mathlib.Tactic

/-!
# ADMITTED RESEARCH-ONLY ENTRY: lower-branch global completion payment

The earlier Hall-G1 route has been formally REFUTED at the true abstract
DirectionData layer: see DirectionDataThreePointG1HallRefutation.lean,
whose axioms have been checked to exclude sorryAx. Its model also
SATISFIES the sharp dyadic capacity at equality, so the failure is
a failure of proposed *subset* Hall expansion, not of the target theorem.

The global payment has now been decomposed into an EXACT certified
rigid-surplus reservation and the TRUE remaining debt:
  unpaidOverlap + profileLoss <= BooleanHoles + netSurplus,
where unpaidOverlap EXCLUDES all one-sided-surplus-paid rigid hard faces
and netSurplus DEDUCTS exactly their verified dyadic face mass.
The rigid-vs-transportable partition, global full-face injection,
rigid nested-cube characterization, one-sided lower-surplus packing,
and the planar implication are all sorry-free kernel-checked results.

Exactly ONE explicit sorry remains, now at the REDUCED global-payment
goal for genuine planar point configurations. The reduction is logically
equivalent to the original lower-branch dyadic target after certified
mass accounting; it is not an independent solution to the hard geometry.
The remaining obligation still includes soft overlaps, the unpaid rigid
corners (equal free dimension or saturated lower endpoint), other
transportable hard overlaps, and projected-profile loss.
No already reserved surplus may be counted a second time.

All theorem statements in this file remain research-only, admitted and
ineligible for award proof submission. The general upper branch and
source-closure obligations remain open as well.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- ADMITTED. The remaining geometric payment obligation is stated
AFTER an independently verified one-sided rigid-surplus reservation.
This reduced payment is still equivalent to the lower-branch capacity. -/
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
  exact planar_lower_branch_dyadic_capacity_of_paid_rigid_remaining
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- THE SOLE ADMITTED GEOMETRIC GOAL IS NOW STRICTLY RESTRICTED TO:
      --   afterRigidPaymentOverlapWords + profileLoss
      --     <= BooleanHoles + (totalSurplus - oneSidedPaidRigidMass).
      -- All removed rigid faces are already kernel-certified surplus-paid.
      -- This remaining inequality is STILL EQUIVALENT to the full
      -- lower-branch conjecture; actual new planar geometry is needed.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
