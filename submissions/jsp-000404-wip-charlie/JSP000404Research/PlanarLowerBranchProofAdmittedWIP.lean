import JSP000404Research.PlanarLowerBranchGlobalPaymentReplacement
import Mathlib.Tactic

/-!
# ADMITTED RESEARCH-ONLY ENTRY: lower-branch global completion payment

The earlier Hall-G1 route has been formally REFUTED at the true abstract
DirectionData layer: see DirectionDataThreePointG1HallRefutation.lean,
whose axioms have been checked to exclude sorryAx. Its model also
SATISFIES the sharp dyadic capacity at equality, so the failure is
a failure of proposed *subset* Hall expansion, not of the target theorem.

This historical WIP has accordingly been redirected to the canonical
GLOBAL completion-mass payment condition:
  overlap + profileLoss <= BooleanHoles + profileSurplus.

Exactly ONE explicit sorry remains, and it is the entire as-yet-unproved
global payment inequality for genuine planar point configurations.
PlanarLowerBranchGlobalPaymentReplacement.lean proves without sorry that
this payment is equivalent to the desired lower-branch dyadic capacity.
Thus reducing two false/overstrong Hall-facing holes to one payment hole
is a proof-ARCHITECTURE correction, NOT a reduction in mathematical
difficulty and NOT a proof of JSP-000404.

All theorem statements in this file remain research-only, admitted and
ineligible for award proof submission. The general upper branch and
source-closure obligations remain open as well.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- ADMITTED. The one remaining geometric payment obligation is
equivalent to the target dyadic lower-branch capacity. -/
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
  exact planar_lower_branch_dyadic_capacity_of_global_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- OPEN GEOMETRY GAP: GLOBAL WEIGHTED COMPLETION PAYMENT.
      -- This is equivalent to the original lower-branch dyadic bound.
      -- Its proof must arise from further genuine planar geometry.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
