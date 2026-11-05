# JSP-000404 original-problem dependency ledger

Restoration date: 2026-11-05. Research only. The original problem is now stated
in Lean, but no theorem proving the full statement exists yet.

## Original statement and acceptance target

For every integer N >= 3, use N distinct points in the real Euclidean plane
and the unoriented angle in [0, pi] at the middle point of a pairwise distinct
triple. Let alpha(N) be the infimum, over those configurations, of their
maximum triple angle; equivalently it is the largest universally forced angle.
Collinear configurations are included. General position and convexity cannot
be added as hypotheses.

The target has BOTH faces:

1. Every configuration has a triple with angle >= a(N).
2. For every epsilon > 0 there is an injective N-point configuration with
   every triple angle < a(N) + epsilon.

Here a(3) = pi/3. For N >= 4 choose the unique n with
2^n < N <= 2^(n+1). The first interval ends at 2^n + 2^(n-2):

- N at or below that endpoint: a(N) = (1 - 2/(2*n+1))*pi.
- N above it: a(N) = (1 - 1/(n+1))*pi.

The power at n=1 must mean a real/integer-exponent power, not natural
subtraction: 2^(1-2) = 1/2. Thus N=4 is in the second interval; N=3 is
handled separately. Dyadic endpoints, both interval boundaries, and epsilon
sharpness must be checked. Attainment by ordinary points is not required.

Sources: upstream catalog at
`f8801a856529dce27e738c6b305e46d76e7c387c`,
[Erdos 504](https://www.erdosproblems.com/504), and Sendov,
*Minimax of the Angles in a Plane Configuration of Points*, Acta Math. Hungar.
69 (1995), 27–46, Theorem 4.1, printed p. 42
([digitized volume](https://real-j.mtak.hu/7467/)). The page image explicitly
has numerator 2. A formula assigned by definition to alpha is not a solution
of the geometric infimum problem.

## Mathematical DAG (statuses distinguish proof from conditional interfaces)

```text
Original all-N equality / lower + epsilon sharpness                  OPEN
|-- geometric extremum definition and exact finite-set correspondence LOCAL PASS
|-- arbitrary-N lower bound                                         OPEN
|   |-- direct unweighted threshold route
|   |   |-- A for every n>=1 via cyclic projection wires             LEAN PASS
|   |   |-- OriginalLowerBound 3 and exact original first branch     LEAN PASS
|   |   |-- B for every n>=2                                         OPEN
|   |   `-- optional affine certificate approach to B                OPEN
|   `-- alternative sufficient weighted route:
|       |-- actual cycles from injective planar points; order/cap transfer
|       |-- lower strip: 0<=delta<1/2, sum 2^k <= 2^n                OPEN
|       |   |-- a top-exponent centre, via one narrow observer      WRITTEN
|       |   |   |-- private-direction weighted interval packing    LEAN PASS
|       |   |   `-- canonical gap exponent -> private directions    WRITTEN
|       |   |-- n=1, n=2; selected small-centre/exact-integer cases   PRESENT
|       |   `-- unrestricted geometric payment or equivalent capacity OPEN
|       |       |-- genuine active choice for projected loss vertices
|       |       |-- terminal / twin / mixed / soft debts
|       |       |-- actual retained-edge covered blockers
|       |       |-- translated-loss duplicate debts
|       |       `-- disjoint payment into actual exterior holes plus
|       |           genuinely unreserved dyadic surplus               OPEN
|       |-- upper strip: 1/2<=delta<1, sum 2^k <= 2^n+2^(n-2)         OPEN
|       |   |-- two top-exponent centres, via two narrow observers  WRITTEN
|       |   |   |-- actual-coordinate narrow-observer bound         LEAN PASS
|       |   |   `-- private-direction weighted residual bound       LEAN PASS
|       |   `-- zero/one top-exponent centre                        OPEN
|       `-- threshold inversion, endpoints, finite maximum            NOT ASSEMBLED
`-- ordinary matching constructions for all N and epsilon > 0        LOCAL PASS
```

`PRESENT` records a source result with historical focused evidence, not a
claim that the entire restored dependency closure currently builds locally.

The construction branch has a complete written ordinary-point proof in
[SHARPNESS_CONSTRUCTIONS.md](SHARPNESS_CONSTRUCTIONS.md). Its corresponding
all-N Lean theorem is now supplied by the pinned, attributed external upper
construction, transported in `OriginalUpperBound.lean`. Source commit
`3acbdd0ad52bebb3dd43dd86d380bf04a6eeb984` builds this target locally with
exit 0 (3,243 jobs). Its four printed statements use only the standard
three axioms. See [EXTERNAL_PROOF_ATTRIBUTION.md](EXTERNAL_PROOF_ATTRIBUTION.md).
The complete original statement is `OriginalProblem`; the proved equivalence
`originalProblem_iff_geometric_alpha_eq` ties it to the genuine geometric
supremum/infimum, without proving the remaining lower bound. The research
umbrella built at clean source `b24bf60107959020e7b29b6e1263b739509987b0`
(9,933 Lake jobs, exit 0). This is a library of results, not a theorem
proving `OriginalProblem`. The separate WIP still depends on `sorryAx`.

The exact remaining lower-strip premise is in
`PlanarLowerBranchActualEdgeCarrierFrontier.lean`:

```text
exists genuinely retained-active choice,
  terminalTwinOtherFiveDebt
  + card(actual same-colour covered blocker union)
  + translatedLossDuplicateDebt
  <= card(lossLedgerOutsideTranslatedTrueHoles)
     + terminalTwinAvailableSurplus.
```

The theorem `planar_lower_branch_capacity_of_actual_retainedEdge_payment`
only consumes this premise. The WIP theorem tries to supply it and leaves
the one executable sorry. `PlanarUpperBranchHardDefect` similarly consumes
an unproved hard-word payment bound with extra allowance 2^(n-2).
Neither conditional implication proves that geometry supplies the premise.

The original unweighted lower problem does not require proving the full
weighted statement for every generalized configuration. In a minimal
overweight induction, the historical unconditional-deletion counterexample
does not settle the issue: its mass is only 7<8. Its fixed-t geometric
realization has now been checked exactly at `t=17/5` (see Section 7 of
[the deletion audit](COMPENSATED_DELETION_HARD_STOP_2026-09-20.md)). A new
restricted deletion-or-capacity argument is still unproved; it must not be
inserted as an assumed induction step.

## Smaller sufficient targets for a replacement route

The original lower bound follows from the following two families for every
integer n>=2 and every finite set of distinct planar points S. Family A now
has a complete Lean proof, also covering n=1. Family B remains open.

    all triple angles < (1-2/(2*n+1))*pi  ==>  |S| <= 2^n
    all triple angles < (1-1/(n+1))*pi    ==>  |S| <= 5*2^(n-2).

For the first interval of the classification, its N is greater than 2^n,
so the first implication gives the required angle by contraposition. For
the second interval, N>5*2^(n-2), and the second implication does the same.
The cases N=3,4 are treated separately. Conversely, the classification's
lower bound at the first integer above either threshold gives the displayed
implication, by taking a subset if |S| is larger. The exact original first
branch and N=3 are proved in `OriginalFirstBranch`.

A strict finite cap at an endpoint can be lowered slightly while still
exceeding all finitely many angles. This is why an open lower strip
delta<1/2 suffices for the first family, and an open upper strip delta<1
for the second. Endpoint equality must not be inserted into an existing
strict-strip lemma. `exists_stronger_angleCap` now certifies this finite-slack
step. All-N sharpness has its separate checked and attributed construction.

The first family already bypasses the weighted payment DAG. The same direct
strategy remains available for B, along with the older optional approaches.

For an ordinary set of the first forbidden size with no three collinear,
[the affine alternative](UNWEIGHTED_AFFINE_THRESHOLD.md) now shows that
forcing the angle throughout its affine orbit is equivalent to a positive
definite average of at most three of its angle matrices with
4 det C >= cot²(lambda). A universal selection theorem for such angles
would suffice for A or B and is **not proved**. The same note proves a
restriction on every minimal A counterexample, tested at n=4. Neither
result depends on a dyadic payment premise.

The proposed shortcut of choosing a common phase with at most one full
direction-band vertex is now FALSE, even for six ordinary integer points
and `t=349/100<7/2`. [The exact certificate](FULL_BAND_PHASE_COUNTEREXAMPLE.md)
checks all 60 angle conditions and every phase cell and endpoint. A second
integer witness also refutes the weaker universal claim that some phase has
full Hansel mass at least `2*|S|-1`: its mass is always between 8 and 10,
while `2*|S|-1=11`. Neither witness refutes the original lower bound.

## Source and public-proof audits

Sendov's Acta Lemma 4.1 (printed pp. 37–40) computes small cases, then states
maximizing exponent profiles for arbitrary s without deriving them from the
induction hypothesis. Independent inspection of pp. 39–40 confirms this
expository gap. Non-comb Kraft equality profiles alone do not disprove an
existential maximizing-profile claim; they only refute uniqueness or a
pointwise profile bound. A replacement capacity proof is still needed.

The assertion alpha(N(a))=a on printed p. 42 cannot hold for all real a:
an integer-valued N(a) is constant on the source's nontrivial intervals.
A generalized-inverse or epsilon argument is needed instead. This is separate
from the deeper geometric capacity gap.

- [#5131](https://github.com/TheJustinSunPrize/awards/pull/5131), aznikline,
  source `cbfbbef188f5f98eead6045d7c3548de3c1b701a`:
  independently read `Statement`, `SmallAngleLower`, `Induction`,
  `CertificateIntegration`, and `MainTheorem`. The final all-N lower theorem
  explicitly takes `GeometricCertificates`; that proposition quantifies the
  overweight deletion/emission certificate for all n>=3. The N<=8 result has
  no such premise. Its all-N upper constructions are attributed to
  superpilot69 and ChatGPT 6 Astra. This session has now independently built
  the 13-module upper closure, excluding `CertificateIntegration`, `Induction`,
  and `MainTheorem`; its lower results have not been independently replayed.
  API state is open, despite a maintainer comment saying
  it is being closed for partial scope; do not infer state from that comment.
- [#100](https://github.com/TheJustinSunPrize/awards/pull/100), zilan520:
  `d869ab901722fab0b2d980b38b7bd958cf52c128` claims exact N=5..10 and all
  dyadic values, including a kernel-checkable nine-point direction certificate.
- [#647](https://github.com/TheJustinSunPrize/awards/pull/647), hit1190100321:
  `2d0c118ba083a5a75609e8dd586e7a478b4a6dab` claims N=11..16 using a
  further finite certificate, with #100's geometric reduction and #42's upper
  constructions. These two claims were read, not independently kernel-replayed
  in this session. They cannot be promoted to arbitrary-n weighted capacity.
- [#300](https://github.com/TheJustinSunPrize/awards/pull/300),
  CollinYuanjieRen, `e80d0b209dc60257c1109ee8ea904ea0d7dd5ef4`, explicitly
  limits its theorem to small N, dyadic values, and all-N construction bounds.

No priority claim or new upstream submission is justified by this audit.

The additional public claim [#4684](https://github.com/TheJustinSunPrize/awards/pull/4684)
was rechecked on 2026-11-05: the PR is closed and unmerged, and its linked
`kunjunsong-code/jsp-000404-lean-proof` repository returns GitHub API 404 to
the available connection. Its stated proof is therefore unavailable for
independent inspection; no proof claim is inferred from its "zero sorry"
description. Fresh searches for JSP-000404 and Erdős 504 found no additional
unconditional all-N source among the returned relevant submissions.

The [Bulgarian Academy bibliography](https://www.math.bas.bg/serdica/bibl.pdf)
also identifies the 1993 Comptes Rendus paper as vol. 46(5), pp. 27-30,
and an exposition in Mathematica Plus (1993), no. 2, pp. 8-13. Bibliographic
metadata, not a verified proof of the general induction, was obtained for
these two items. An actual missing derivation would change this assessment.

Three additional public research repositories were inspected at fixed
commits on 2026-11-05. None supplies the missing arbitrary-N lower bound:

- [Jackie1021](https://github.com/Jackie1021/jsp000404-lean/tree/3e8b0127db073a4d5b7f2baea478b2e1abfb904e),
  `3e8b0127db073a4d5b7f2baea478b2e1abfb904e`: the source of
  `GlobalDirections.cardinality_bound` gives s <= 2^k under t <= k.
  Taking the ceiling at noninteger t is too weak. The completion contract
  proves an equivalence with six obligations, not those obligations.
  The reported five-row deletion obstruction is a direction model;
  real planar coordinates are not asserted. No local rebuild is claimed.
- [DF-dan](https://github.com/DF-dan/jsp-000404-sendov-audit/blob/33c3c3eff9a6de37ecc00ecb34ad4e451f56a0ba/lean/Branch17Certificate.lean),
  `33c3c3eff9a6de37ecc00ecb34ad4e451f56a0ba`: the 17-row theorem
  `branch_forces_half_step` assumes ten specified triangle-order
  inequalities before proving t >= 9/2. Other order choices are not
  excluded by this statement. No local rebuild is claimed.
- [jerrylijize1224-star](https://github.com/jerrylijize1224-star/jsp404-lean-partial/tree/09b2ee9cab2da6ca977f682f1c8359b5e90d13d0),
  `09b2ee9cab2da6ca977f682f1c8359b5e90d13d0`: the 2026-11-04
  snapshot has the same Lean/Mathlib pins. The ZIP SHA-256 is
  `34839c6043eedccec8b383823aeb65f7479ec5496e2d230d4e715a8c6d12e9b0`;
  all 762 manifest entries were verified without extracting a worktree.
  Inspection of `Basic`, `Target`, `SeventeenTwentyExact`, and
  `TwentysevenExact` confirms the ordinary finite-set definitions and the
  exact ranges of the theorems: 17..20 at 7*pi/9 and 27..32 at 4*pi/5.
  Its own log reports a 3,280-job build; 2,711 printed axiom entries were
  found in its supplied audit. These are **publisher logs**, not a local
  Lean replay. The project credits #100 and #647 for earlier finite cases.
  It leaves 21..26 between 140 and 144 degrees and its full `SendovClaim`
  as an unproved proposition.

The November snapshot also contains an obstruction directly relevant to the
second threshold at n=4. Its *abstract* 21-row family has nine single-arc
and twelve three-arc rows, period 18, and diameter <= 43/6 < 36/5.
Our [independent rational checker](scripts/check_public_arc_obstruction.py)
reconstructs the intervals from the published starts; it does not execute
any archived program or rely on the stored solver witnesses. All 210 pairs
have antipodal intersections. Thus row diameter and pairwise compatibility
alone do not imply the desired bound of 20. For rows 7, 9, 10, every
permitted direction choice satisfies w<u<v and v-w<9. But the direction
of the sum of the two nonparallel edges, v, must lie strictly between u
and w on their common open half-circle. This contradiction excludes the
fixed model from the plane, not all 21-point configurations. The model and
the discovery of this obstruction belong to that cited project; only the
independent check is ours. The third-party archive is not committed.

## Excluded shortcuts

The [separate-affine-map width-drop recursion](AFFINE_PARTITION_OBSTRUCTION.md)
also fails on twenty integer points at t=23/5. A rational cover by 296 angle
matrix certificates shows that every bipartition has a part whose every affine
image exceeds the child cap at t-1=18/5. All parent angles pass exact arithmetic.
The full geometric counterexample is written and executable; its Lean geometry
is pending. It respects the original capacity twenty and leaves an assertion
restricted to minimal overweight configurations open.

The retained historical witnesses rule out unconditional compensated deletion,
unique-comb or pointwise-comb assertions, coarse support-only capacity, arbitrary
local collision refunds, and unrestricted reuse of one opposite Boolean word.
An abstract bipartite K5 colouring can have active profile 3,3,2,2,2 and a
unique C4; a bad vertex can be pendant to that C4. A convex-C4 lemma cannot
therefore be applied without proving convexity and incidence. None of these
countermodels is itself a counterexample to the original planar statement.

A stronger wide-sector shortcut also fails for arbitrary circular edge
labels. In lexicographic edge order on vertices 0..5, take the labels
`3,0,2,6,9,8,7,13,11,12,1,14,10,5,4` modulo 15, in units of pi/15.
For a triangle T let D(T) be 15 minus its largest circular gap. Over all
20 triangles, min D(T)=5. Yet
`max_s min_T max_{a in T} (1 + ((a-s-1) mod 15)) = 7`, for s=0..14
and a ranging over T's three edge labels. Thus for a phase s+x, 0<=x<1,
some triangle has all its labels at forward offsets in [1-x,7-x]. Every
open sector of width (3/2)*5 contains a triangle. This refutes only that
uniform 3/2 strengthening from per-triangle circular-span data, not the
smaller width required at a particular t. The order of the 15 labelled
crossings admits no one of the 720 starting vertex permutations for which
all crossings swap adjacent projections. It is not a planar witness.
An [ordinary Euclidean construction](UNWEIGHTED_SECTOR_COUNTEREXAMPLE.md)
now disproves the universal wide-sector premise for all n>=64, even at
the smaller width pi/n. It leaves an overweight-only claim undecided.

The [new five-cycle check](UNWEIGHTED_ROW_CYCLES.md) rules out every
18-row subset of the fixed 21-row model, including a four-row obstruction
in which all triples are separately realizable. There is still no
universal exclusion of a geometric 21-point counterexample to B(4).

Credit supply or direct weighted capacity would suffice on the weighted
route. The direct unweighted route has no such prerequisite.

New exact geometric witness: [UPPER_FOUR_CENTRE_COUNTEREXAMPLE.md](UPPER_FOUR_CENTRE_COUNTEREXAMPLE.md)
rules out the stronger four-centre fixed-parameter upper bound 2^n+2^(n-3).
Unlike a merely abstract Kraft profile, it gives four rational points, all
actual triple angles, and every projective gap and floor. A separate written
two-level binary-circle construction gives a perfect GC with ten leaves and
exact GA=11*pi/15, refuting the source's printed four-centre maximum of nine.
Neither construction is Lean-certified yet; the full upper bound of ten is
respected, and the original classification is not refuted.

New recursion audit: [WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md](WIDTH_DROP_PARTITION_COUNTEREXAMPLE.md)
gives five integer points at t=10/3 and t=15/4 for which no two-colouring produces two
unchanged subsets with AngleCap at t-1. All ten angle witnesses are checked
by strict integer dot-product inequalities. Any width-drop recursion would
need a genuinely new direction-changing construction and a proof that it
preserves the needed geometric invariants. The same note now proves failure
for every 3<t<4 by a five-point binary-family limit argument; restricting
the unchanged-subset recursion to the upper strip does not fix it.
It now also gives an ordinary sixteen-point family for every t>4. Two
separated direction pairs make 272 designated binary-word triples too large
for the child cap, and every two-colouring contains one such triple. A
uniform angular-error estimate proves the Euclidean realization. An explicit
set in Q(sqrt(2)) works at both t=17/4 and t=19/4; all 65,536 colourings were
checked with integers. Thus adding small base cases and starting this
unrestricted unchanged-subset step at n>=4 also fails. No minimal-overweight
property is established for these witnesses, so a step restricted to that
domain is not refuted by them. The isolated t=4 is not
settled by these counterexamples. These are written/executable certificates,
not Lean geometry theorems or a counterexample to the original problem.

## Completed cyclic-wire proof of family A

The [direction-order proof](CYCLIC_WIRE_RETIMING.md) proves threshold A
through an embedded cyclic projection graph. Its checked dependency chain is

1. Construct consecutive projection-wire arcs from an arbitrary strict-cap set.
2. Extract disjoint continuous graph paths from each simple cycle.
3. Apply the reflected-strip return theorem to bound winding by two.
4. Convert the original strict delays to nonpositive integral cycle weights.
5. Erase loops and construct an integer event-time potential.
6. Sum incident-wire delays and encode the retimed signs in n Boolean bands.

All six steps are connected for actual planar point maps. The principal
modules and their roles follow.

- `CyclicWireLocalGaps` derives the incident-time inequalities and cardinality
  code from consecutive integer delays and the reflected closing delay.
- `CyclicWireGraph` defines the adjacent and closing arrows, proves strong
  connectivity from shared pair events, and composes the retiming and coding
  theorems with its simple-cycle winding premise.
- `OrderedDirectionWires` builds sorted incident event lists from DirectionData
  with injective local values. It proves event coverage, opposite pair signs,
  and strict source delays after scaling from t<n+1/2.
- `ProjectionStrictWireDirections` supplies local injectivity from the actual
  positive AngleCap through the existing generic projection bridge.
- `WireCurveTrace` constructs continuous lifted walks with half-open arrow
  provenance. `WireCurveEmbedding` proves source separation from the exact
  pair-crossing property. `SimpleWireCycle` uses path simplicity to obtain
  disjoint period pieces, and `PeriodicCycleOrder` bounds their number by two.
- `ProjectionWireCurves` proves the actual trigonometric intersection formula.
  `OrderedDirectionCurves` uses it to discharge the concrete graph's winding
  premise from the forward polar lift.
- `PlanarFirstThreshold` proves the complete ordinary family A, including
  finite strict-cap slack and all small-cardinality cases. `OriginalFirstBranch`
  proves `OriginalLowerBound 3` and the exact first interval of `alphaN`.

The umbrella imports the complete first-threshold chain. Its proof uses
`propext`, `Classical.choice`, and `Quot.sound`. Focused evidence is in
`verification/first-threshold-20261105/`. The half-integer-period capacity
required for B and the remaining full-scope acceptance work stay open.

For B, the unrestricted coherent unit-collapse induction remains a conjecture.
Its strengthened requirement that all events inside the chosen interval cross
between colours has an exact nine-wire all-phase counterexample. That example
still permits a free-colour collapse, and preserves the full B(4) capacity.

The [independent-set representation candidate](HALF_GRID_INDEPENDENT_SET_RESEARCH.md)
offers a second B route. Half-grid rows would extend, preserving their signs,
to distinct maximal independent sets of a triangle-free graph on 2n+1
coordinates. The required graph count is the Hujter–Tuza bound. Four finite
graph certificates have independent exact checks. The stronger claim for
every fixed schedule is now refuted by a coherent nine-wire certificate,
with all triangle-free graphs and all coordinate polarities exhausted.
A canonical retiming of that same order has a valid encoding. The
arbitrary-configuration selection of retiming and representation remains open.
