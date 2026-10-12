import JSP000404Research.PlanarLowerBranchTerminalHardNetReduction
import Mathlib.Tactic

/-!
# ADMITTED RESEARCH-ONLY ENTRY: EXPLICIT terminal rigid hard net-payment frontier

Exactly ONE executable sorry remains, with an increasingly precise
geometric obligation for the genuine planar AngleCap point model.

Certified non-reusing reservations: full hard-face payments; ascending
rigid lower-surplus payments; descending rigid upper-surplus payments.
After those deductions, the leftover hard Boolean words are EXACTLY
a disjoint union of outgoing/inactive TRANSPORTABLE hard faces and
RIGID faces whose BOTH endpoints have saturated projected budgets.

Unlike the previous net goal's opaque hard remainder, the currently
admitted inequality has the explicit five-source left hand side:
  soft overlap Boolean words
    + unreserved TRANSPORTABLE hard Boolean words
    + SUM of UPPER target masses of terminal doubly saturated RIGID pairs
    + SUM of LOWER target masses of ascending mixed rigid pairs
    + SUM of UPPER target masses of descending mixed rigid pairs
    + projected profile loss.
Payment must come ONLY from TRUE Boolean holes and the total dyadic
surplus remaining after all three certified non-reusing reservations.

A full-face injective transport of the movable hard words does EXIST,
but its images are singleton/soft COVERED words, NOT necessarily holes.
The terminal rigid pairs have zero local surplus, so a new global
geometric argument is essential.

The new equivalence and genuine-plane conditional bridge are fully
kernel-checked independently without sorryAx; THIS theorem retains
the one explicit sorryAx. The deficit inequality remains EQUIVALENT
to the unproved lower-branch capacity; the JSP-000404 prize problem,
general upper branch, and source closure are NOT solved here.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- ADMITTED. The only outstanding planar input is now precisely
the terminal transportable Boolean mass, terminal saturated rigid
upper target debt, both mixed-rigid target debts, soft mass and loss
versus true holes and NET unreserved surplus. -/
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
  exact planar_lower_branch_dyadic_capacity_of_terminal_hard_net_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- SOLE OPEN GEOMETRIC INPUT:
      -- soft overlap + net TRANSPORTABLE hard overlap
      -- + terminal DOUBLY SATURATED rigid upper-target dyadic debt
      -- + both mixed-rigid strict-endpoint dyadic target debts
      -- + projected-profile loss
      -- <= TRUE Boolean holes + genuinely UNRESERVED surplus.
      --
      -- All intermediate word disjointness, dyadic mass accounting,
      -- one-layer planar budget and conditional bridge are certified
      -- without sorryAx. This global geometric payment remains open.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
