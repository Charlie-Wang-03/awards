import JSP000404Research.PlanarLowerBranchTerminalTwinNetReduction
import Mathlib.Tactic

/-!
# ADMITTED RESEARCH-ONLY ENTRY: TWIN-ONLY terminal rigid debt frontier

The genuine planar AngleCap lower branch is reduced to EXACTLY ONE
unproved global defect-payment inequality. There is ONE executable
`sorry` in this module; `#print axioms` must report `sorryAx`.
No full JSP-000404 proof or disproof is claimed.

All earlier whole-face hard surplus, ascending mixed-rigid lower
surplus, and descending mixed-rigid upper surplus reservations are
certified non-reusing.

A NEW global hard carrier VERTEX MATCHING proof shows all hard
carriers pairwise share no centre. Terminal doubly-saturated rigid
pairs further have an EXACT exhausted dichotomy:

  1. upper target exponent STRICTLY BELOW lower target exponent:
     a reverse-safe colour exists on the upper endpoint, inactive
     on the lower. The ENTIRE strict-descending face is transported
     by a globally injective flip into singleton/soft COVERED words;
  2. EQUAL target exponents:
     both endpoint completion cubes and all incoming/outgoing
     retained-incidence palettes are LITERALLY IDENTICAL.
     These are the final TWIN rigid faces left by both tested
     forward and reverse whole-face transport mechanisms.

The true outstanding six-source inequality is now explicitly:

  softOverlapWords
    + netOutgoingTransportableHardWords
    + netReverseStrictDescentRigidHardWords
    + SUM_twinRigid 2^k(upper)
    + SUM_ascendingMixed 2^k(lower)
    + SUM_descendingMixed 2^k(upper)
    + projectedProfileLoss
  <= TRUE Boolean holes
    + total dyadic surplus - already reserved full-hard mass
                           - ascending lower-surplus credit
                           - descending upper-surplus credit.

Both forward and reverse movable hard maps are individually GLOBAL
injections, but their images are NOT certified DISJOINT; all output
words are already COVERED and cannot be counted as Boolean holes.
Consequently no unproved payment cancellation is permitted.

The six-source net goal is formally equivalent to the previous
five-source goal and to the original lower-branch conjecture. The
equivalence and planar conditional bridge are certified sorry-free,
but the actual global payment remains a genuine mathematical gap.
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
  exact planar_lower_branch_dyadic_capacity_of_terminal_twin_net_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- SOLE OPEN GEOMETRIC INPUT: true Boolean holes and genuinely
      -- unreserved surplus must pay for soft overlap, BOTH forward
      -- and reverse movable hard Boolean masses, equal-target TWIN
      -- rigid dyadic weight, both mixed-rigid target debts and loss.
      -- Forward/reverse images are COVERED and may intersect.
      -- The global geometric payment is NOT proved; this sole sorry
      -- is retained intentionally with sorryAx.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
