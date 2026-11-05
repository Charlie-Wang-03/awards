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
