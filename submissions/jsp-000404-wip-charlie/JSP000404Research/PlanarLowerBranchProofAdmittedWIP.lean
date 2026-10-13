import JSP000404Research.PlanarLowerBranchTerminalTwinNetReduction
import JSP000404Research.PlanarForwardReverseBridgeDyadicCapacity
import JSP000404Research.PlanarBridgeSoftStrictDyadicGap
import JSP000404Research.PlanarStrictShellSoftMassLedger
import JSP000404Research.PlanarStrictShellReserveLedger
import JSP000404Research.PlanarNetActualCollisionPaymentFrontier
import JSP000404Research.PlanarIncomparableBridgeCapacity
import JSP000404Research.PlanarIncomparableBridgeDensityCapacity
import JSP000404Research.PlanarIncomparableBridgeLowerExponent
import JSP000404Research.PlanarActualCollisionTwoBitBridgeCapacity
import JSP000404Research.ResidualBridgeDiagonalTrueHoleLedger
import JSP000404Research.ResidualTwoFlipTargetedTrueHoleLedger
import JSP000404Research.ResidualTwoFlipSourceEndpointBlocker
import JSP000404Research.ResidualActualCollisionDiagonalExactObstruction
import JSP000404Research.ResidualTwoFlipDiagonalGlobalCollisionRigidity
import JSP000404Research.ResidualNetCollisionCertifiedMobilePayment
import JSP000404Research.ResidualNetCollisionCertifiedBlockerClassification
import JSP000404Research.ResidualNetCollisionCertifiedGlobalLedger
import JSP000404Research.ResidualNetCollisionCertifiedDiagonalWitness
import JSP000404Research.ResidualNetCollisionVariableDiagonalLedger
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
injections. Their common sink words are SOFT and have a UNIQUE
oriented residual bridge owner (reverse lower, forward upper).
The candidate bridge soft pool has exactly the summed DYADIC mass
  SUM_bridge 2^card(commonRetainedInactive).
Consequently the two movable hard classes together are bounded by
  singleton + soft + bridge-soft;
this is now a verified actual AngleCap planar theorem, available
below as `hmobile`.

NEW verified shared-cube and exact strict dimensional-descent bounds
show that bridge-soft candidate mass and reverse strict-rigid source
mass inhabit one disjoint family of lower completion cubes. In
genuine planar AngleCap this gives the auxiliary theorem `hbridgeGap`:

  SUM_bridge 2^commonInactive
  <= SUM_strictRigid 2^k(lower) - SUM_strictRigid 2^k(upper).

This dyadic DIMENSION GAP is not `dyadicProfileSurplus`: both
endpoints of terminal rigid carriers are saturated. One may NOT
deduct it again as already-unreserved surplus without an additional
proved global allocation theorem.

The two images are NOT proven DISJOINT. All sink words are already
COVERED and cannot count as TRUE Boolean holes. The new bridge
bound by itself does NOT establish the net-payment inequality.
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
two certified movable hard source masses (subject to a global
singleton/soft/bridge dyadic sink bound), equal-exponent TWIN
rigid dyadic target debt, both mixed-rigid target debts, soft mass
and loss versus TRUE holes and NET unreserved surplus. -/
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
  have hmobile :=
    planar_mobile_hard_mass_le_singleton_soft_bridge_dyadic
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  have hbridgeGap :=
    planar_bridge_soft_dyadic_mass_le_strict_target_descent_gap
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  have hlocalShellMass :=
    planar_strict_shell_singleton_soft_local_mass_ledger
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  have hglobalShellReserve :=
    planar_strict_shell_singleton_bridge_nonbridge_exact_ledger
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  have hnetPaymentFrontier :=
    planar_net_unpaid_mobile_payment_iff_actual_sink_credit
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  have hpaletteFilteredMobile :=
    planar_net_mobile_mass_plus_unused_le_incomparable_bridge_dyadic
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  have hpaletteQuarterMobile :=
    planar_net_mobile_mass_plus_unused_le_incomparable_bridge_density
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  have hbridgeLowerExponent :=
    planar_net_actual_collision_twice_le_strict_lower_target_sum
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  have htwoBitFilteredMobile :=
    planar_net_mobile_mass_plus_unused_le_two_bit_bridge_dyadic
      hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
  exact planar_lower_branch_dyadic_capacity_of_terminal_twin_net_payment
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- SOLE OPEN GEOMETRIC INPUT: true Boolean holes and genuinely
      -- unreserved surplus must pay for soft overlap, BOTH forward
      -- and reverse movable hard Boolean masses, equal-target TWIN
      -- rigid dyadic weight, both mixed-rigid target debts and loss.
      -- Verified planar hmobile bounds both movable source classes
      -- by singleton + soft + the exact dyadic BRIDGE-SOFT pool.
      -- Verified planar hbridgeGap bounds that candidate bridge mass
      -- by the strict-rigid LOWER-minus-UPPER dyadic descent budget.
      -- That bound is already in context, but its targets are COVERED,
      -- not TRUE holes. It does not pay the remaining global debt.
      -- Verified planar hlocalShellMass is the STRONGER exact per-carrier
      -- partition: strict lower shell = singleton-covered mass plus
      -- full outgoing soft-overlap carrier dyadic mass. This does not
      -- turn either covered class into unreserved surplus or true holes.
      -- Verified planar hglobalShellReserve sharpens hbridgeGap to
      -- EXACT three-way global conservation: shell SINGLETON plus
      -- candidate BRIDGE plus NONBRIDGE SOFT = strict dyadic gap.
      -- All categories are COVERED; none is a true-hole credit.
      -- Verified planar hnetPaymentFrontier is an EXACT IFF with the
      -- remaining net-unpaid mobile masses, using the ACTUAL net
      -- image intersection and the UNUSED singleton/soft sink credit.
      -- Unlike the old coarse bridge upper bound, it explicitly
      -- excludes paid forward hard sources and unrealized collisions.
      -- New hpaletteFilteredMobile also removes EVERY candidate
      -- bridge-soft carrier whose endpoint active palettes are nested.
      -- Only incomparable-palette SOFT bridge dyadic faces survive
      -- as possible NET hard transport collision mass, with the
      -- unused covered sink reserve explicitly retained.
      -- New hpaletteQuarterMobile shows the stronger STRUCTURAL
      -- codimension restriction: each surviving bridge face has
      -- at most n-2 common inactive coordinates and at most
      -- 2^(n-2) Boolean words, giving a purely carrier-count bound.
      -- This is a candidate collision upper bound, NOT a
      -- true-hole credit or an unreserved profile surplus.
      -- Certified hbridgeLowerExponent improves the ambient n-bound
      -- to the SATURATED strict lower target k(b), giving each
      -- incomparable bridge at most HALF of its own Q_b dyadic mass.
      -- The sum is still indexed by BRIDGES; multiple bridges may
      -- share lower b, so it is NOT an independent profile payment.
      -- htwoBitFilteredMobile excludes MORE impossible soft carriers:
      -- beyond the incomparable active palettes, the canonical
      -- retained Boolean codes of reverse lower b and forward upper
      -- v must disagree at >=2 distinct retained coordinates.
      -- The independently proved actual NET collision lower-shell
      -- partition also prevents reusing strict-rigid lower targets.
      -- All surviving sink words remain COVERED, not true holes.
      -- The certified two-flip diagonal is OUTSIDE the two bridge
      -- endpoint cubes. Its overlap cube injects into that LOCAL
      -- exterior, and the new exact local hole ledger proves
      -- overlap <= GLOBAL true holes + third-centre-covered exterior.
      -- Third-centre external coverage is an EXPLICIT, UNPAID
      -- obstruction. It may not be discarded as zero or called
      -- genuinely unreserved surplus. Moreover hole targets across
      -- different bridges have no proven global disjoint allocation.
      -- The new exact selected-diagonal ledger refines that coarse
      -- exterior-cover obstruction: for any fixed bridge/flip pair,
      -- OVERLAP mass = TRUE-HOLE diagonal mass + COVERED diagonal mass.
      -- Every COVERED diagonal is certified to have an EXTERNAL centre
      -- with the OPPOSITE canonical retained bit at cf or cr.
      -- The new exact collision-diagonal obstruction IFF makes the
      -- global hole criterion completely explicit: BOTH original
      -- source-side cross-activities and exclusion of EVERY fifth
      -- or later covering centre are necessary and sufficient
      -- for THIS ONE diagonal to be a true Boolean hole.
      -- This is not a non-reusing allocation across collisions.
      -- Rigidity of the double-flip diagonal across DIFFERENT chosen
      -- flip pairs is now proved: equal diagonal targets require the
      -- underlying collision sink words to agree outside the four
      -- flip coordinates. A FIXED flip pair has no duplicate images.
      -- Different-pair hole images have a joint non-reusing bound
      -- IF their source sets differ at an outside-four coordinate
      -- for EVERY cross-class pair, and each target is a true hole.
      -- Neither hypothesis is presently derived from planar AngleCap,
      -- and no automatic global hole-credit cancellation follows.
      -- New ACTUAL-COLLISION obstruction: the double-flipped corner
      -- equals reverseFlip(original forward HARD source) and ALSO
      -- forwardFlip(original reverse strict-rigid HARD source).
      -- If reverse colour is inactive at forward lower a, Q_a covers
      -- the diagonal; if forward colour is inactive at reverse upper
      -- z, Q_z covers it. Hence a GLOBAL hole requires simultaneous
      -- cr ∈ retainedActive(a) AND cf ∈ retainedActive(z).
      -- These are NECESSARY conditions, NOT a guarantee of a hole.
      -- In particular the true-hole diagonal budget cannot be
      -- inferred from the earlier two-cube exterior injection alone.
      -- If this specific opposite-bit blocker type can be excluded,
      -- the entire overlap face injects into global TRUE holes.
      -- The planar exclusion of such blockers, plus disjointness of
      -- hole assignments across different bridges and payments for
      -- twin/mixed/loss terms, remains UNPROVED.
      -- This rigorously sharpens the SHAPE of the final obligation,
      -- but neither side has been proved geometrically from holes
      -- and genuinely unreserved profile surplus.
      -- NEW kernel-checked ACTUAL NET collision map and conservation:
      -- each collision sink has a UNIQUE original forward and reverse
      -- hard source by the two existing globally injective transports.
      -- Their genuine chosen flip colours give a deterministic
      -- canonical opposite diagonal, not an arbitrary bridge face.
      -- The complete NET collision cardinal is EXACTLY:
      -- DISTINCT true-hole diagonals + DISTINCT covered diagonals
      -- + duplicate-image hits for source-dependent flip colours.
      -- Replacing the collision mass in exact net mobile-source
      -- conservation yields a certified 5-term mobile ledger.
      -- Every COVERED canonical diagonal has a certified blocker:
      -- source-side cross-inactivity OR a fifth-or-later covering
      -- centre with an opposite retained-bit signature.
      -- Neither covered-target mass nor duplicate hits are shown
      -- payable by TRUE holes or UNRESERVED dyadic profile surplus.
      -- The twin/mixed/soft/loss debts are also not cancelled.
      -- The global geometric payment is NOT proved; this sole sorry
      -- is retained intentionally with sorryAx.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
