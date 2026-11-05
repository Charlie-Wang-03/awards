# Half-grid signs and maximal independent sets

2026-11-05, after the completed family-A checkpoint `449be4d2`. Family B
remains open. The fixed-schedule representation proposed at `727fc926` now
has an exact coherent counterexample, even allowing arbitrary coordinate
polarity choices and any triangle-free graph. The version selecting a prior
retiming remains open and survives that counterexample.

## The matching extremal numbers

Hujter and Tuza proved that a triangle-free graph on q>=4 vertices has at most
`2^(q/2)` maximal independent sets when q is even, and
`5*2^((q-5)/2)` when q is odd. The odd extremizer is a five-cycle together
with disjoint edges. Substituting q=2n+1 gives exactly the missing family-B
constant. This theorem motivates the representation below. Its application
to projection wires still requires a new mathematical argument.
[Hujter–Tuza, SIAM Journal on Discrete Mathematics 6 (1993), 284–288](https://doi.org/10.1137/0406022).

## Signed rows on the half-grid

Take a coherent weak cyclic schedule with period q/2, where q>=5 is odd,
and double its times. Every event has an integer time h. At each endpoint,
let s be its original movement bit and assign the signed bit

    b = s XOR (h mod 2)

to coordinate h mod q. The naming of positive and negative bits is arbitrary,
and a common reversal of every bit is allowed. Let P_v and N_v be the sets
of coordinates assigned positive and negative signs at wire v.

Consecutive doubled unit delays equal two. The incident gap consequences
give absolute differences at most q, same-sign differences at most q-2,
and opposite-sign differences at least two. Thus b is well-defined at a
coordinate, including event times differing by q. If two adjacent cyclic
coordinates had the same b at one wire, their lifted time difference would
be one or q-1 in absolute value. The first case would have opposite original
signs and violate the lower bound two. The second would have equal original
signs and violate the upper bound q-2. Hence both P_v and N_v are independent
sets of the coordinate cycle C_q.

Every two original wires share an event with opposite endpoint signs.
Consequently

    (P_v intersect N_w) union (N_v intersect P_w) is nonempty.

Any binary completions preserving these specified signs are therefore
distinct. The local statements above have written proofs from the checked
cyclic-delay algebra. Their odd-period packaging has not yet been added to
the Lean chain.

## Proposed representation

Starting with the coordinate cycle C_q, repeatedly remove two adjacent
remaining vertices and record them as a separate edge. Stop with an odd
cycle of length at least five. Keep that residual cycle in its inherited
cyclic order, together with all recorded disjoint edges. Call the resulting
graph H. Its maximum degree is two and it is triangle-free.

The initial strong candidate asserted that for every coherent half-grid schedule,
some such H and one common choice of sign polarity let every signed row
extend to a maximal independent set I_v of H, with

    P_v subset I_v, and I_v intersect N_v empty.

The opposite-sign overlap makes v ↦ I_v injective. The graph bound would then
give `|V| <= 5*2^((q-5)/2)`. The fixed-schedule assertion is false by the
counterexample below. A weaker statement allowing a suitable prior retiming
of each actual planar projection graph would also suffice for the original
problem. Its construction remains open.

For these particular H, one can also count directly. A disjoint edge
contributes a factor two, and an odd residual cycle of length r>=5 has at
most `5*2^((r-5)/2)` maximal independent sets. This avoids a need to formalize
the full graph theorem once the representation is established.

The target is a counting representation. The complement of a maximal
independent set may contain adjacent vertices. Consequently these codes
impose different conditions from preserving every child unit delay after a
common interval collapse. The existing nine-wire forced-colouring obstruction
itself admits such an encoding, as verified below.

## Exact finite evidence

`scripts/check_half_grid_independent_encoding.py` uses only the standard
library. It checks all triangle constraints, reconstructs a complete
adjacent-swap reversal refinement, verifies the signed rows and cyclic-pair
deletion, enumerates all maximal independent sets of H, and checks the
distinct sign-preserving codes. Four complete certificates are retained in
`verification/independent-encoding-20261105/examples.json`.

| Schedule | q | Wires | Residual cycle | Recorded edges | MIS count |
| --- | --- | --- | --- | --- | --- |
| Independently synthesized sharp schedule | 7 | 10 | 5 | 1 | 10 |
| Twenty-point affine-obstruction order after retiming | 9 | 20 | 5 | 2 | 20 |
| Nine-wire forced-interval-colouring obstruction | 9 | 9 | 5 | 2 | 20 |
| Uniform seven-wire polygon schedule | 7 | 7 | 7 | 0 | 7 |

The uniform seven-wire schedule requires allowing a larger residual odd
cycle in this fixed-sign proposal. Exhausting all labelled C5+K2 graphs
and both polarities found no encoding for those rows. The full C7 supplies
one. A different feasible retiming of its order does admit a C5+K2 encoding.

Additional exploratory outputs remain in ignored `artifacts/`.

- All 91 canonical arrays with odd q>=7 in the 779-array collection admitted
  a triangle-free graph of maximum degree two. The 66 arrays with
  q in {7,9,11,13} also admitted the more specific cyclic-pair-deletion form.
- The specific form passed 442 distinct varied-potential arrays at q=7 or 9.
  The search discarded 478 duplicate arrays. It also passed 80 distinct
  signed-row arrays obtained from 190 roots and 100 random initial bounds
  on the sharp twenty-point order.
- A finite-domain solver synthesized 1,000 distinct coherent ten-wire
  schedules at q=7. Every one admitted a C5+K2 encoding. This enumeration
  explored a finite subset of the possible schedules.
- The earlier geometrically impossible twelve-row subsystem admits no
  triangle-free encoding under either common polarity according to the
  solver. The same holds for the full twenty-one-row example. These UNSAT
  results have no independent proof certificate yet. They help distinguish
  the global representation claim from the already-false local-row relaxation.

Search tools are `probe_maximal_independent_encoding.py`,
`probe_cycle_smoothing_encoding.py`, `solve_independent_encoding.py`, and
`probe_sat_independent_encoding.py`, all under `artifacts/`. The corresponding
JSON audits retain the tested rows and successful graph certificates.

## Other falsification work in this continuation

A targeted solver query produced a coherent nine-wire schedule at q=7 that
excludes every proposed fixed-sign graph. The independent checker
`scripts/check_half_grid_encoding_obstruction.py` verifies its 84 triangle
constraints and explicit 36-event adjacent-swap reversal. For each of the
128 coordinate-polarity choices, any admissible graph edge must avoid
co-occurrence among the forced positive coordinates. This reduces the full
graph search to 22,752 polarity/edge-subset choices. All 21,328 triangle-free
choices fail to extend at least one row to a maximal independent set.
This excludes every triangle-free graph on the seven coordinates, including
graphs outside the cyclic-pair-deletion family.

The original polarity allows nine possible graph edges, and its complete
reversal allows eight. Their 512 and 256 edge-subsets already refute the
original common-polarity proposal. The larger exhaustive check also covers
independent flips of individual coordinates.

The same cyclic wire order has a canonical greatest feasible potential below
the all-zero initial upper bounds. Its period remains 7/2. That retiming
admits the five-cycle `(0,3,4,5,6)` and separate edge `(1,2)`, after a common
sign reversal. The checker verifies every original consecutive delay and
closing delay for the new times, then verifies all nine distinct MIS codes.
Thus a theorem selecting a retiming remains viable. The fixed-schedule
obstruction and its explicit repair are retained under
`verification/independent-encoding-obstruction-20261105/`.

A targeted follow-up generated 1,000 distinct coherent nine-wire time arrays
that all defeat the fixed cyclic-pair-deletion encoding. Rebuilding their
wire graphs with an adjacent-swap tie refinement and taking the canonical
greatest feasible potential produced only five distinct signed-row arrays.
All five admit the encoding. The local audit is
`artifacts/canonical-encoding-repair-audit.json`. This supports investigating
the canonical selection rule, while its universal proof remains open.

The freely coloured unit collapse also succeeds on the obstructing schedule
at phase 1/2. Its nine wires respect the original B(3) ceiling of ten.
Euclidean realization of this newly synthesized abstract order is unverified.

At q=9, a further targeted query found a seventeen-wire fixed-schedule
obstruction to cyclic-pair-deletion encodings. Its canonical retiming admits
the five-cycle `(0,1,2,7,8)` and edges `(3,4)` and `(5,6)`. A subsequent
200-array targeted run produced four distinct canonical signed-row arrays,
all with successful encodings. The outputs are
`artifacts/canonical-encoding-repair-17.json` and
`artifacts/canonical-encoding-repair-17-9-audit.json`.

Free-colour interval collapse survived 982 distinct varied feasible schedules,
with 698 duplicates discarded. It remains a separate unproved route.

The bounded integer event-array model at N=11, q=7 returned UNSAT in about
one second, both with and without triangle betweenness. N=10, q=7 returned
SAT and supplied the first certificate above. N=21, q=9 timed out after
180 seconds. These runs fixed event (0,1) at zero. They supply exploratory
solver outcomes, without a universal theorem or a kernel certificate.

The bounded signed-gap relaxation at N=21, q=9 now has an explicit exact
counterexample. Orienting the earlier twenty-one rows by a topological order
of their forced projection relation and choosing one allowed bearing for
each pair gives all 1,330 signed-gap triple constraints, but violates
betweenness on 127 triples. The data are in
`artifacts/bounded-signed-gap-21-explicit.json`. A separate finite signed-row
solver also found 21 compatible rows with an acyclic ambient-order relation.
Thus adding a total ambient order to the local signed-gap conditions is
insufficient. Any replacement graph construction must use stronger global
coherence or actual geometry.

The guess that every odd critical optimum equals half the original convex
hull size fails. Among 46 actual-point odd-optimum inputs, 44 had a different
hull size. For example, an eight-point input has q=7 and a six-point hull.
The sharp twenty-point example has a nine-vertex hull and a nine-unit
critical cycle, which motivated the failed guess. A universal convex-hull
reduction should therefore be dropped.

## A local criterion for the canonical clock

The following argument identifies a precise selection rule to investigate.
It supplies no graph encoding yet.

Use integer doubled period q, with q odd. Place the cut immediately after
phase zero and normalize event clocks into `(-q,0]`, so phase-zero events
have clock zero and other phases j have clock j-q. A wire arc e from u to v
has nonnegative wrap m_e and delay d_e in {0,1}, with

    H_u <= H_v + q*m_e - 2*d_e.

Call the arc tight when equality holds. Suppose every event with negative
clock has an outgoing tight arc. Follow these arcs. A path either reaches
a zero-clock event or enters a directed cycle. A cycle consisting entirely
of zero-delay tight arcs would have zero total wrap and is excluded by the
original strictly increasing event order. Every other tight cycle advances
its phase by two for each unit-delay arc. Since q is odd, a closed sequence
of these advances visits every residue, including zero. Thus every event
has a tight path to a zero-clock event.

For any feasible competitor K with all K_e<=0, telescope the upper-bound
inequalities along that tight path. Its endpoint has K<=0, while H has value
zero. The resulting inequality is K_e<=H_e at the starting event. Therefore
H is the greatest feasible clock under the all-zero upper bounds.

Conversely, a greatest integer clock must have an outgoing tight arc at
every negative event. Otherwise all of that event's finitely many outgoing
integer inequalities have slack at least one. Increasing just its clock by
one preserves them and the zero upper bound, while incoming inequalities
become easier. This contradicts greatestness. The argument uses the ordinary
consecutive-event quiver with at least two distinct events per wire.

The criterion can be expressed in a finite-domain search with event phases
in {0,...,q-1}. Give tied events a rank consistent with every triple's crossing
order. A nonzero event must have either a later same-phase event on one of
its wires, or an incident event exactly two phase units ahead cyclically
with the appropriate movement-sign change. The signed-gap bounds ensure
that an incident tight pair expands to tight consecutive arcs.

Adding this criterion to the targeted encoding-counterexample query returned
UNSAT at N=9, q=7 in about 1.8 seconds. The corresponding N=17, q=9 query
timed out after 180 seconds. Both searches fix event (0,1) at phase zero.
These solver outputs have no kernel or independent UNSAT certificate. The
criterion's argument above is written mathematics, and its Lean proof and
the general encoding construction remain outstanding.

The current targeted search is
`artifacts/refute_smoothing_encoding.py --canonical`. A proof should explain
how this tight-edge structure yields an encoding, or identify a counterexample
to that implication. The successful experiments alone leave that implication
open.

## Critical-root potentials

A second selection rule removes the exceptional zero-clock sinks. At the
minimum feasible period, choose an event on a zero-total-weight critical
cycle. Assign each event the minimum upper-bound path weight from it to
that chosen root. Strong connectivity makes the path family nonempty.
Nonnegative cycle weights allow loop erasure, so a shortest path exists.
Prepending an arrow gives every required difference inequality, and the
first arrow of a shortest path is tight. At the root, the critical cycle
has total slack zero, so its outgoing arrow is tight too. Thus every event
has an outgoing tight arrow.

This is the min-plus eigenvector condition for the cyclic constraint graph.
The graph construction and its one/two-turn cycle theorem make the optimum
the maximum of a finite nonempty family of integer or half-integer cycle
ratios. In particular, the optimum is attained. If that optimum is at most
the integer n, integer potentials and the checked signed-band packing give
cardinality at most 2^n. The remaining B case has optimum exactly n+1/2 and
can use the critical-root selection above.

Testing this rule on 61 retained odd-period orders with q in {7,9,11,13}
gave a cyclic-pair-deletion MIS encoding in every case. The sharp twenty-point
order and the targeted seventeen-wire obstruction also passed. The stronger
forced-active-bit collapse rule failed at source indices 41, 305, 419, 526,
and 590, and on the seventeen-wire example. The proposed MIS representation
therefore remains the relevant target for this selection rule. The audit is
`artifacts/critical-eigen-encoding-audit.json`.

The tight graph had exactly one cyclic strongly connected component in all
71 odd-optimum inputs from the original 599-order collection. Among its
528 integer-optimum inputs, four had two cyclic components and the other
524 had one. These observations suggest a possible additional odd-period
structure theorem, which is unproved and is unnecessary for existence of a
critical-root potential. The data are `artifacts/odd-critical-components.json`
and `artifacts/even-critical-components.json`.

The search flag `--harmonic` in `refute_smoothing_encoding.py` requires an
outgoing tight continuation even at phase-zero events. Tied-event order is
read directly from each triangle's crossing order, eliminating auxiliary
event-rank variables. The N=17, q=9 encoding query returned UNKNOWN after
300 seconds. The N=21, q=9 overweight coherent-schedule query returned
UNKNOWN after 1,200 seconds. Neither timeout decides its mathematical claim.

## Consecutive cores fail even for critical-root clocks

All 66 original retained encoding arrays, 442 varied-potential arrays, and
63 critical-root arrays admitted a five-cycle on five consecutive coordinates
with the remaining coordinates paired. This suggested restricting the core
to a single consecutive block. A targeted search refuted that restriction.

There are now exact witnesses with N=11, q=11 and N=17, q=9. Each has an
explicit adjacent-swap reversal, all triangle inequalities, a feasible
clock, a tight critical cycle of winding two, and a tight path from every
event to a chosen event on that cycle. The paths prove that the displayed
clock, after subtracting its root value, is the shortest-path potential to
that root. Every outgoing clock inequality is checked, and every event has
an outgoing tight arc. The critical-cycle equality also proves optimality
of the period for that fixed cyclic wire order.

For every cyclic block of five coordinates and either common polarity,
some row has no compatible maximal independent set on its five-cycle.
The standard-library checker enumerates all five maximal independent sets
for each core. Thus the restriction fails for a selected critical-root
clock itself. The greatest all-zero-upper-bound clocks of these same two
orders also failed the exploratory consecutive-core test.

Both witnesses have valid sparse five-cycle encodings. In the supplied
phase normalization, the eleven-wire example uses core `(0,1,2,7,8)` and
pairs `(3,4)`, `(5,6)`, `(9,10)`. The seventeen-wire example uses core
`(1,2,3,6,7)` and pairs `(0,8)`, `(4,5)`. These graphs have respectively
40 and 20 maximal independent sets. Their codes are checked independently.
The new abstract orders' Euclidean realizations have not been established.

The certificates, path witnesses and reproduction instructions are in
`verification/critical-clock-core-20261105/`. The checker is
`scripts/check_critical_clock_core_obstruction.py`. The general selected-
retiming encoding remains open.

## Reducing cyclic pair deletion to the core alone

The matching can always use edges of the original coordinate cycle.
Indeed, after cyclic adjacent-pair deletion, each gap between successive
retained core vertices contains an even number of deleted vertices. Pair
those vertices consecutively within each gap. These pairs are adjacent in
the original cycle. Conversely, such even gaps provide an explicit valid
deletion sequence. Equivalently, the cyclic distances between consecutive
core vertices are all odd.

For every row, its positive and negative supports are independent in the
original cycle. It therefore extends to exactly one chosen endpoint of
each new matching edge. If an endpoint is positive it must be chosen, and
if one is negative its neighbor can be chosen. The two endpoints cannot
both be positive or both negative. If neither endpoint is prescribed,
either choice works. Choices on separate matching edges are independent.

Consequently, existence of an encoding after cyclic pair deletion is
equivalent to existence of an odd core of size at least five, with all
cyclic gaps odd, such that every signed row extends to a maximal independent
set of the core cycle under one common polarity. Nested matching edges
provide no additional possibilities. The restricted size-five candidate
needs only five possible core codes per row. This yields a substantially
smaller countersearch than enumerating all matching completions.

For a consecutive five-coordinate core, the original four path edges
already make the positive and negative supports independent. Its only
minimal forbidden partial patterns, with dots denoting unspecified entries,
are `+...+` and `-.+.-`. These patterns explain the targeted search above.
The general five-coordinate core need not retain these four original edges,
so its checker must test all five maximal independent sets directly.

## Next mathematical obligation

Construct a suitable retiming and graph H jointly, or refute a specified
selection rule such as the canonical greatest potential. The fixed-schedule
form is excluded and should be abandoned. A possible source of additional
structure is an optimal half-grid potential and its embedded tight-edge
graph. The graph-potential and simple-cycle theorems are already checked,
but they currently supply no independent-set representation.

Any eventual proof must retain the full quantifier over actual configurations
and account for the selection of retiming, common polarity, and cyclic pair
deletions. The observed graph certificates provide concrete targets for that
construction. Formalizing a generic conditional graph-count implication alone
would leave this central obligation open.
