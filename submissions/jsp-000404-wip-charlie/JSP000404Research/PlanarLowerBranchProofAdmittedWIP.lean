import JSP000404Research.PlanarLowerBranchExternalHoleFrontier
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
import JSP000404Research.ResidualNetCollisionCertifiedDuplicateWitness
import JSP000404Research.ResidualNetCollisionExactHammingObstruction
import JSP000404Research.ResidualNetCollisionSupportFibreMultiplicity
import JSP000404Research.ResidualNetCollisionExactFibreDebt
import JSP000404Research.ResidualNetCollisionFibreDebtPartition
import JSP000404Research.ResidualNetCollisionBridgeFibreCapacity
import JSP000404Research.ResidualNetCollisionDoubleShellBridge
import JSP000404Research.ResidualNetCollisionTargetShellBridgeFibre
import JSP000404Research.ResidualNetCollisionFourBitBridgeEndpointSeparation
import JSP000404Research.ResidualNetCollisionCrossRoleEndpointSeparation
import JSP000404Research.ResidualNetCollisionSharedVertexTwoBitClassification
import JSP000404Research.ResidualNetCollisionSharedVertexInactiveCapacity
import JSP000404Research.ResidualNetCollisionFixedEndpointColourInjection
import JSP000404Research.ResidualNetCollisionTargetBridgeColourSlots
import JSP000404Research.ResidualNetCollisionExactShellColourSlots
import JSP000404Research.ResidualNetCollisionExactShellPaymentBound
import JSP000404Research.ResidualFiniteBipartiteCoverCapacity
import JSP000404Research.ResidualNetCollisionExactShellBipartiteCover
import JSP000404Research.ResidualNetCollisionMatchingObstruction
import JSP000404Research.ResidualNetCollisionFullMatchingCertificate
import JSP000404Research.ResidualNetCollisionMaximumMatchingPayment
import JSP000404Research.ResidualNetCollisionRainbowMatchingCapacity
import JSP000404Research.ResidualNetCollisionRainbowPairObstruction
import JSP000404Research.ResidualNetCollisionCandidateColourVertexSeparation
import JSP000404Research.ResidualNetCollisionCandidateShadowCompletion
import JSP000404Research.ResidualNetCollisionCandidateShadowInjection
import JSP000404Research.ResidualNetCollisionRainbowRedundancyAudit
import JSP000404Research.ResidualNetCollisionLocalSoftSphereCapacity
import JSP000404Research.ResidualNetCollisionLowColourNoDuplicate
import JSP000404Research.PlanarNetLowColourNoDuplicate
import JSP000404Research.ResidualNetCollisionThreeColourTwoBitObstruction
import JSP000404Research.ResidualNetCollisionEightCentreBarrier
import JSP000404Research.PlanarNetSmallCentreNoDuplicate
import JSP000404Research.ResidualNetCollisionVertexBudgetFibre
import JSP000404Research.ResidualNetCollisionAllBitBridgeVertexSeparation
import JSP000404Research.ResidualNetCollisionOriginalBridgeVertexMatching
import JSP000404Research.ResidualNetCollisionOriginalBridgeMatchingDominance
import JSP000404Research.ResidualNetCollisionNineCentreRigidExhaustion
import JSP000404Research.PlanarNetNineCentreTwinTradeoff
import JSP000404Research.PlanarNetElevenCentreTwinCapacity
import JSP000404Research.ResidualNetCollisionSupportOverlapLaw
import JSP000404Research.ResidualTwoFlipExactHammingCases
import JSP000404Research.ResidualNetCollisionExactFlipSupport
import JSP000404Research.ResidualTwoFlipExactSymmetricDifference
import JSP000404Research.ResidualNetCollisionCertifiedBlockerClassification
import JSP000404Research.ResidualNetCollisionCertifiedGlobalLedger
import JSP000404Research.ResidualNetCollisionCertifiedDiagonalWitness
import JSP000404Research.ResidualNetCollisionVariableDiagonalLedger
import JSP000404Research.ResidualNetCollisionElevenCentreDoubleHit
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
  -- The exact six-source terminal debt has been algebraically reduced
  -- without strengthening AngleCap or manufacturing hole credit.
  -- This application leaves precisely the EXTERNAL-hole payment open:
  -- non-loss debt + translated-covered blockers + duplicate debt
  -- <= TRUE holes OUTSIDE translated loss slices + unreserved surplus.
  exact planar_lower_branch_capacity_of_external_loss_obstruction
    hp hcap hn hdelta0 hdeltaHalf ht hlam cycles
    (by
      -- SOLE OPEN GEOMETRIC INPUT (exact equivalent reduced form):
      -- outside-translated TRUE holes and genuinely unreserved surplus
      -- must pay all other terminal debts, globally covered translated
      -- loss blockers, and cross-coordinate translated duplicate debt.
      -- The translated loss TRUE holes have already been cancelled
      -- from both sides using the verified exact loss conservation.
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
      -- NEW: positive duplicate debt is now certified to imply two
      -- DISTINCT actual net sink-collision sources with one common
      -- canonical diagonal. Such sources agree at every coordinate
      -- OUTSIDE their four genuinely chosen transport flip colours.
      -- A planar exclusion or separate credit for those exact
      -- four-coordinate pairs is the OPEN next proof target.
      -- Neither covered-target mass nor duplicate hits are shown
      -- payable by TRUE holes or UNRESERVED dyadic profile surplus.
      -- The twin/mixed/soft/loss debts are also not cancelled.
      -- EXACT DOUBLE-FLIP SYMMETRIC DIFFERENCE (NEW):
      -- if two canonical actual sink collision words hit the SAME
      -- diagonal target, their DIFFERENCE COORDINATES are EXACTLY
      -- the symmetric difference of their two original unordered
      -- 2-colour flip supports, not merely a subset of four colours.
      -- Hence same unordered colour support implies the same source:
      -- the canonical map is injective INSIDE EACH support fibre.
      -- A strictly POSITIVE duplicate debt forces TWO distinct
      -- genuine NET sink words of Hamming distance exactly 2 OR 4,
      -- from DIFFERENT canonical unordered flip-colour supports.
      -- This closes odd-distance and same-support cases ONLY.
      -- Planar AngleCap exclusion/payment of the remaining
      -- 2-bit/4-bit cross-support pairs is still OPEN.
      -- NEW actual 2-colour support-intersection conservation:
      -- equal canonical diagonals give source Hamming distance
      -- PLUS twice the common-colour intersection size EXACTLY FOUR.
      -- Thus 2-bit duplicate sources share ONE original colour,
      -- while 4-bit duplicate sources have DISJOINT colour pairs.
      -- The pair (canonical diagonal, unordered chosen colour set)
      -- is a globally INJECTIVE tag of each actual NET source.
      -- Every target fibre has cardinal <= Nat.choose n 2,
      -- and |NET collisions| <= Nat.choose n 2 * |distinct diagonals|.
      -- These are overlap/finite-multiplicity bounds, NOT a proof
      -- that the actual diagonals are holes, disjoint payments,
      -- or that the remaining covered/duplicate debt vanishes.
      -- NEW EXACT SOURCE-FIBRE DEFECT ACCOUNTING (verified):
      -- the global actual canonical duplicate debt is the exact SUM
      -- of (genuine source-fibre size - 1) over EACH distinct diagonal.
      -- This sum is explicitly split by TRUE Boolean hole diagonals
      -- and ALREADY-COVERED diagonals, with no duplicated hole credit.
      -- The resulting NET forward/reverse mobile-source equation is
      -- a fully checked hole+covered+excess-fibres conservation law.
      -- Each individual fibre is bounded by Nat.choose n 2 and
      -- its distinct sources differ by original 3-colour or
      -- 4-colour collision motifs; neither motif is yet excluded.
      -- Geometric payment of BOTH classes of fibre excess,
      -- plus source-side/fifth-centre covering, twin/mixed/soft
      -- and projected-loss budgets, remains OPEN.
      -- STRONGER ORIGINAL-BRIDGE DIAGONAL RIGIDITY:
      -- ANY two ACTUAL NET sinks with the SAME original soft bridge
      -- and the SAME canonical diagonal are EQUAL, even if their
      -- original hard flip colours differ. Thus a POSITIVE duplicate
      -- debt necessarily witnesses DIFFERENT original soft bridges.
      -- Every actual bridge owner lies in the doubly filtered
      -- incomparable-active / >=2-bit discrepancy soft bridge pool.
      -- EVERY actual diagonal source fibre therefore has cardinal
      -- <= the card of that GENUINE candidate bridge carrier pool,
      -- as well as <= Nat.choose n 2 (the older colour-support cap).
      -- Globally |NET| <= |distinct diagonals| * |bridge carriers|.
      -- This is an honest COVERED bridge capacity, NOT true-hole
      -- or independent unreserved profile-surplus credit.
      -- Under the EXTRA assumption that at most ONE such bridge
      -- carrier exists, duplicate debt is zero; planar AngleCap
      -- does NOT currently imply that additional assumption.
      -- NEW EXACT TARGET-DEPENDENT DOUBLE-SHELL OBSTRUCTION:
      -- For each ACTUAL NET source collision, its canonical diagonal
      -- violates EXACTLY ONE retained-active bit at EACH original
      -- SOFT bridge endpoint: the actual forward / reverse flip.
      -- These coordinates are EXCLUSIVE to their respective
      -- endpoints, giving a target-specific eligible bridge pool.
      -- Each actual diagonal source fibre injects into THAT
      -- target-dependent pool, never just the global bridge pool.
      -- If every ACTUALLY HIT target admits at most one such eligible
      -- bridge, duplicate-image debt vanishes; planar AngleCap
      -- has NOT been shown to imply this conditional uniqueness.
      -- Under same-diagonal reuse, equal reverse-lower endpoints
      -- force equal original forward colours; equal forward-upper
      -- endpoints force equal original reverse colours. Therefore
      -- 4-BIT duplicate-source pairs must differ at BOTH
      -- SAME-ROLE soft bridge endpoints, not necessarily at all four
      -- centres across cross-roles. Geometric exclusion/payment
      -- of remaining CROSS-bridge motifs remains OPEN.
      -- NEW CROSS-ROLE / SHARED-VERTEX STRUCTURAL OBLIGATIONS:
      -- Equal canonical diagonals plus CROSS-ROLE shared source
      -- bridge vertices force equality of corresponding original
      -- forward/reverse transport colours. Thus FOUR-bit repeated
      -- sources require all FOUR source-native bridge endpoints to
      -- be PAIRWISE DISTINCT (not just distinct in their own roles).
      -- Two DISTINCT same-target sources whose original bridges
      -- share ANY vertex instead have EXACTLY TWO different bits
      -- and exactly ONE original flip colour in common. Both sink
      -- words inhabit the completion cube of the common vertex,
      -- so that vertex has AT LEAST TWO inactive Boolean coordinates.
      -- Inactive dimension <=1 excludes shared-vertex duplication
      -- there, but NO planar AngleCap theorem currently guarantees
      -- that all candidate bridge endpoints have this dimension.
      -- Vertex-disjoint four-bit and two-bit patterns and remaining
      -- higher-dimensional shared-vertex motifs remain to be PAID
      -- or excluded, with fifth-centre, twin, mixed, soft, loss debt.
      -- NEW EXACT ENDPOINT-COLOUR-SLOT DUPLICATE CAPACITIES:
      -- Within any target d and original lower vertex b, the
      -- source-native original reverse flip colour is INACTIVE at b
      -- and INJECTIVELY labels the ACTUAL sources, as the original
      -- forward flip is FIXED by the exact singleton violation.
      -- The upper vertex v has the dual forward-colour injection.
      -- Hence fixed-endpoint target source mass is bounded by its
      -- retained-INACTIVE colour count (LINEAR, not 2^dimension).
      -- Globally each genuine NET source fibre D^-1(d) injects
      -- separately into target-compatible LOWER and UPPER
      -- vertex/inactive-colour slots, L(d) and U(d), with endpoint
      -- eligibility certified by existing double-shell soft bridges.
      -- With original eligible bridge candidates B_2(d),
      -- |D^-1(d)| <= m(d) := min(|B_2(d)|,|L(d)|,|U(d)|).
      -- Exact duplicate debt E_D <= SUM_(d IN D(I))(m(d)-1)
      -- follows from the previously proved exact fibre ledger.
      -- The theorem "m(d)<=1 for EACH ACTUALLY HIT d => E_D=0"
      -- is CONDITIONAL. Planar AngleCap does NOT yet prove that
      -- condition; no covered SOFT target or slot is a literal
      -- TRUE Boolean hole or already-unreserved dyadic surplus.
      -- NEW TARGET-EXACT OTHER-ENDPOINT VIOLATION SLOT FILTER:
      -- Previous eligible lower/upper vertex-colour slots permitted
      -- ANY retained-inactive colour at the listed endpoint,
      -- regardless of whether it was the ACTUAL opposite endpoint's
      -- uniquely violated active bit at this target d.
      -- L*(d),U*(d) impose BOTH that exact violation requirement AND
      -- the genuine candidate double-shell bridge compatibility.
      -- Every ACTUAL source fibre D^-1(d) injects separately into
      -- L*(d) and U*(d); both are PROVED subsets of the older
      -- L(d),U(d), so the triple target-specific minimum
      -- m*(d) = min(|B_2(d)|, |L*(d)|, |U*(d)|) <= m(d).
      -- The full certified duplicate debt is bounded by
      -- SUM_(d IN D(I)) (m*(d)-1). This has been substituted into
      -- the REAL NET MOBILE HARD SOURCE PAYMENT inequality against
      -- only LITERAL true Boolean holes, genuine singleton/soft
      -- covered mass, DISTINCT already-COVERED diagonals, and
      -- the EXPLICIT exact-shell duplicate excess. Covered targets
      -- are NOT silently holes; neither slot pool is a hole or
      -- independently unreserved dyadic profile surplus.
      -- Geometric payment/exclusion of all cross-bridge targets,
      -- fifth-centre covered diagonals, twin, mixed-rigid, soft
      -- and projected loss debts remains GENUINELY OPEN.
      -- VERIFIED NON-REUSED BIPARTITE SLOT COVER CAPACITY:
      -- For each ACTUAL canonical diagonal target d construct
      -- genuine-source-compatible exact-shell bridge edges between
      -- LOWER slots (original lower, reverse flip) and UPPER slots
      -- (original upper, forward flip). Every true NET collision
      -- produces one ALLOWED edge, with separate injectivity
      -- of lower and upper endpoint slot labels at fixed d.
      -- For ANY finite candidate edge-vertex cover A(d),B(d),
      -- the ACTUAL fibre cardinal is <= |A(d)|+|B(d)|.
      -- Each source is charged ONCE via disjoint Sum.inl/inr tags.
      -- Consequently E_D <= SUM_(d IN D(I))
      --   (|A(d)|+|B(d)|-1), provided the cover property holds
      -- on EVERY eligible target-edge graph. The bound is substituted
      -- into the literal-hole/covered-target/mobile-hard ledger.
      -- This may be sharper than min(|B_2(d)|,|L*(d)|,|U*(d)|)
      -- when the eligible bipartite graph is sparse, BUT finding
      -- small enough covers under real AngleCap and paying them
      -- from genuinely UNRESERVED resources are OPEN obligations.
      -- A covered SOFT edge or endpoint SLOT is NEVER a TRUE hole.
      -- Certified two-edge matching obstruction (matching-free graph
      -- implies zero NET duplicate debt): see
      -- ResidualNetCollisionMatchingObstruction.lean. Any two ACTUAL
      -- same-diagonal sources imply two eligible edges with DISTINCT
      -- lower and upper colour slots. Deriving geometric matching
      -- exclusion (or paying such matchings from nonreused resources)
      -- remains OPEN; no matching-free hypothesis is silently assumed.
      -- SOURCE-COMPATIBLE GRAPH CORRECTION: eligible candidate edges
      -- now additionally require reverse colour INACTIVE at their
      -- own lower endpoint and forward colour INACTIVE at their
      -- own upper endpoint. Prior source-inclusion remains certified.
      -- Every candidate edge has both target-exact slot endpoints;
      -- the derived maximum matching number is for this STRICTER
      -- finite graph, not arbitrary coloured endpoint pairs.
      -- None of these edges or matching capacities is a TRUE hole.
      -- AUDITED RAINBOW MATCHING CONDITION:
      -- Every ACTUAL target-diagonal source fibre embeds at EXACT
      -- size into an eligible matching with DISTINCT lower/upper
      -- slots and DISTINCT unordered original flip colour PAIRS.
      -- LATER CANDIDATE SHADOW-INJECTION AUDIT proves that these
      -- pairs are ALREADY distinct for ALL eligible candidate
      -- edges, including ones without hard-source provenance.
      -- Thus rho(d) = nu(d), a verified equality: the rainbow
      -- constraint gives NO strict graph capacity improvement.
      -- A positive actual duplicate debt still forces two
      -- slot-disjoint candidate edges with DIFFERENT colour pairs;
      -- in the actual exact-shell graph ALL distinct edges differ
      -- in this pair. Hence excluding those pairs is simply
      -- ordinary two-edge matching exclusion, NOT a weaker gate.
      -- Remaining geometry must pay/exclude matching components,
      -- plus fifth-centre, twin, mixed-rigid, soft and profile debt.
      -- NEW CANDIDATE EDGE --> COVERED SOFT SHADOW CERTIFICATES:
      -- Every eligible target-exact bridge edge, even without any
      -- ACTUAL hard-source provenance, gives a canonical double-flip
      -- shadow word lying in BOTH retained completion cubes.
      -- Its bridge is an ordered SOFT overlap carrier, so the
      -- shadow belongs to the genuine already-COVERED soft words.
      -- Because each completion word has at most TWO covering
      -- vertices, the oriented bridge is uniquely determined by
      -- the shadow; at FIXED target d, the exact singleton violated
      -- active colours uniquely recover BOTH edge endpoint slots.
      -- Thus target-exact candidate EDGES inject into ACTUAL soft
      -- overlap words: |E(d)| <= |softOverlapCompletionWords|.
      -- This is only PER TARGET; shadow words can be reused across
      -- different d and are NOT true Boolean holes. Neither this
      -- injection nor the Rainbow Matching bounds supplies an
      -- unreserved global six-source payment budget. The missing
      -- AngleCap allocation, fifth-centre, twin, mixed, soft and
      -- projection loss debts remain unproved.
      -- NEW TARGET-LOCAL SOFT SPHERE CAPACITY:
      -- Every candidate edge's shadow differs from target d at
      -- EXACTLY TWO bit positions, and is a genuine SOFT word.
      -- Since ordinary nu(G_d) <= |E(G_d)| <= local soft count,
      -- MIN(nu(G_d), local soft count) = nu(G_d) IDENTICALLY.
      -- Thus MIN-bound rewrites do NOT shrink earlier NET duplicate
      -- debt estimates. This explicitly corrects the previous
      -- overclaim of an independent local-sphere improvement.
      -- Single local soft shadow per hit d implies zero NET debt;
      -- that conditional criterion is NOT proved from AngleCap.
      -- No new true hole credits or global nonreused payments.
      -- GENUINE SMALL-n NET DUPLICATE ELIMINATION (n<=2):
      -- Since a true source fibre injects into the choose(n,2)
      -- unordered flip-colour supports, there can be at most ONE
      -- actual source per canonical target for n<=2. The actual
      -- canonical diagonal map is globally injective in this
      -- regime and actual duplicate debt = ZERO unconditionally.
      -- For n<=1 the entire genuine NET collision set is empty.
      -- This is an authentic closed debt SUBCASE, not another
      -- equivalent matching bound. The covered target blockers
      -- and the independent twin/mixed/soft/profile debts remain.
      -- FIRST UNRESOLVED SMALL-n COLLISION MOTIF (n=3):
      -- With <=3 Boolean colours, positive ACTUAL NET duplicate
      -- debt forces two distinct same-diagonal source sinks with
      -- EXACT Hamming distance TWO, and their unordered canonical
      -- two-flip colour supports have intersection CARDINALITY ONE.
      -- Four-bit/disjoint-support duplicates are impossible here.
      -- These are real Lean-checked necessary conditions, NOT a
      -- geometric exclusion of the remaining two-bit witness.
      -- NEW ALL-n SOURCE-NATIVE EIGHT-CENTRE BARRIER:
      -- Any two actual distinct NET sources with the SAME canonical
      -- target have two different forward hard carriers and two
      -- different reverse rigid hard carriers. These FOUR hard
      -- carriers are distinct, and all hard carriers form a
      -- vertex matching. Therefore positive duplicate debt
      -- FORCES at least EIGHT original centres, regardless of n.
      -- For |V| <= 7 this exact debt is ZERO; covered-blocker,
      -- soft, rigid and profile debts remain unpaid.
      -- NEW ACTUAL ALL-BIT SOFT-BRIDGE ENDPOINT EXCLUSION:
      -- Four original hard carriers for any distinct same-target
      -- NET sources form a vertex matching, so even their TWO
      -- induced soft bridge owners are VERTEX-DISJOINT in all
      -- lower/upper and CROSS-ROLE combinations. This upgrades
      -- the older four-bit-only separation to the surviving
      -- TWO-BIT case. In n<=3, positive NET duplicate debt
      -- requires TWO fully vertex-disjoint SOFT bridges with
      -- exactly one original flip-colour overlap. No AngleCap
      -- geometric exclusion of this residual remains proved.
      -- FURTHER ORIGINAL-VERTEX MATCHING GEOMETRIC GATE:
      -- Every real same-target NET source fibre embeds at EXACT
      -- CARDINALITY into the original-centre VERTEX MATCHING of
      -- original soft bridges projected from target-exact
      -- (vertex,colour) slot edges. This condition is stronger
      -- than a slot matching: candidate edges may be slot-disjoint
      -- but still share an ORIGINAL centre and cannot both be
      -- genuine duplicate sources. A targetwise pairwise-intersecting
      -- eligible original bridge graph would therefore force ZERO
      -- duplicate debt, but that hypothesis has NOT been proved
      -- from planar AngleCap and is NOT inserted into this goal.
      -- ORIGINAL-VERTEX vs COLOURED SLOT DOMINANCE AUDIT:
      -- EVERY vertex-disjoint candidate original SOFT bridge
      -- matching lifts (via a chosen eligible slot edge per
      -- bridge) to a SAME-CARDINALITY ordinary slot matching.
      -- Thus nu_original_vertex(d) <= nu_slot(d) for ALL targets.
      -- The new genuine NET bound
      -- |F_d| <= min(nu_original_vertex(d), floor(|V|/4))
      -- is PROVED no weaker than the previous slot + quarter
      -- bound. Strictness is NOT claimed for all configurations.
      -- SMALL-VERTEX ACTUAL COLLISION EXHAUSTION:
      -- For <=9 original centres, TWO distinct same-target NET
      -- sources consume ALL FOUR possible original hard carriers.
      -- Every terminal NET rigid pair is one of the two
      -- STRICT-descending reverse sources, hence no EQUAL-exponent
      -- twin-rigid term survives IF positive duplicate debt occurs
      -- in this regime. The remaining covered SOFT and global
      -- geometric payment obligations are not thereby closed.
      -- FORMAL SMALL-VERTEX TWO-DEBT MUTUAL EXCLUSION:
      -- For <=9 original centres, E_D (genuine NET duplicate
      -- image excess) and T (equal-exponent TWIN rigid dyadic
      -- mass) CANNOT BOTH BE POSITIVE: E_D * T = 0 and
      -- E_D + T = max(E_D,T). The SAME identity is now a
      -- genuine planar AngleCap theorem built from centre cycles
      -- and one-layer residual evidence. When E_D>0, ALL terminal
      -- rigid hard words are strict-descending reverse movable
      -- hard words; no TWIN face survives. This is conditional
      -- on <=9 original centres and not a complete global payment.
      -- The global geometric payment is NOT proved; this sole sorry
      -- is retained intentionally with sorryAx.
      sorry)

#print axioms planar_lower_branch_dyadic_capacity_admitted_wip

end ProjectionOrdered
end JSP000404Research
