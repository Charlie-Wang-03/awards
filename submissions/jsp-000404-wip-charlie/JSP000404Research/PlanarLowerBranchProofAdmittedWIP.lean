import JSP000404Research.PlanarLowerBranchAscendingNetPaymentReduction
import Mathlib.Tactic

/-!
# ADMITTED RESEARCH-ONLY ENTRY: NET ascending-rigid payment frontier

The original loss-free subset-Hall claim is refuted at the abstract
DirectionData layer; it is not used in this entry.

The previously kernel-verified global accounting pays complete hard
overlap faces whenever their two endpoint surpluses suffice. New
verified matching lemmas additionally reserve the LOWER surplus of
unpaid rigid faces with STRICT lower endpoint and saturated upper
endpoint. Their FULL intersection mass is exactly:
  lower dyadic surplus + lower target weight.

Exactly ONE executable sorry remains at the further NARROWED planar
net-payment goal:

  softOverlapWords
    + (unpaidHardOverlapWords minus ascendingRigidWords)
    + SUM ascendingRigid lower target weights
    + projectedProfileLoss
  <= genuine Boolean holes
    + totalSurplus - alreadyPaidFullHardMass
                   - ascendingRigidPartialCredit.

All subtractions are natural-number net reservations. The new
accounting interface formally proves the nonreuse budget and
equivalence to the older lower-branch target. No surplus can
be counted a second time.

This remaining inequality is mathematically EQUIVALENT to the
lower-branch capacity: this file is NOT a complete proof.
The general upper branch and source-closure obligations remain open.
No award-eligible theorem is claimed.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- ADMITTED. The remaining geometric payment obligation is stated
AFTER verified whole-face hard payments AND globally nonoverlapping
partial payments of ascending rigid faces.
The reduced net payment remains equivalent to the lower-branch target. -/
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
  exact planar_lower_branch_dyadic_capacity_of_net_ascending_rigid_remaining
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- SOLE OPEN GEOMETRIC INPUT:
      -- soft overlap + nonascending unpaid hard overlap
      -- + one lower target weight per ascending rigid carrier + profile loss
      -- <= true Boolean holes + net surplus after BOTH reservations.
      --
      -- All reductions, whole-face matching and partial reservations
      -- are independently kernel-checked with NO sorryAx.
      -- This outstanding inequality is still EQUIVALENT to the true
      -- lower-branch dyadic capacity, NOT a solved theorem.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
