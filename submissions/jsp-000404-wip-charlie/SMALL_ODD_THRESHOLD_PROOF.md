# Unconditional small odd-phase thresholds

2026-11-05. The Lean chain proves the right-angle bound for four points,
the 120-degree bound for six points, and the 135-degree bound for eleven
points. Together with the general first threshold, these give the exact
original lower bound for every 3 <= N <= 20. The general second threshold
for n >= 4 remains open.

## From actual points to signed rows

The actual projection-curve and simple-cycle construction is the one proved
in `CYCLIC_WIRE_RETIMING.md`. Let q be 3, 5, or 7. A strict cap at
`pi-pi/((q+1)/2)` gives a non-strict cap with positive slack, because there
are finitely many admissible triples. Its width is strictly below (q+1)/2.
Scale the concrete direction events to that larger source period. All
consecutive and closing inequalities become strict, including zero delays.

The checked one-or-two-turn theorem and half-grid retiming then supply
integer event times H with doubled period q. Along each wire the times
are nondecreasing, opposite consecutive movement signs cost at least two,
and the reflected closing constraint has cost two when the endpoint signs
agree. For any two events on that wire these imply

    |H_f-H_e| <= q;
    equal movement signs imply |H_f-H_e| <= q-2;
    opposite movement signs imply |H_f-H_e| >= 2.

For the last implication, monotonicity and a gap smaller than two force
all intermediate consecutive signs to agree. For the equal-sign upper
bound, a span greater than q-2 leaves gaps smaller than two at both ends
of the wire. Its endpoint signs therefore agree and the closing constraint
forces a contradiction. This argument is formalized in `OddWireSchedule`.

Assign an incident event to coordinate H modulo q, with bit equal to its
movement sign when H is even and the opposite sign when H is odd. Since q
is odd, events on the same wire with equal residue give equal transported
bits: a nonzero possible difference is q, and the closing bound forces
opposite movement signs. Events at neighboring residues give opposite bits;
the small difference has equal movement signs and the possible long
difference has opposite movement signs. The finite q cases are checked by
integer arithmetic in `SmallOddWireCapacity`.

Choose one event at each occupied coordinate. This produces a partial
two-colouring of the q-cycle, with neither bit repeated on adjacent occupied
coordinates. Every pair of wires shares its actual pair event and has
opposite movement signs there. Their partial rows thus prescribe opposite
bits at some common coordinate. No event or pairwise separation is lost.

## The three finite capacities

On the three-cycle, every valid partial row extends to a full binary word
whose positive set is a singleton. There are three such words. On the
five-cycle, every valid partial row extends to a word whose positive set
is `{i,i+2}` modulo five. There are five such words. These two complete
finite statements are proved by ordinary Lean `decide`. Two separated rows
cannot extend the same word. Their cardinalities are therefore at most
three and five respectively.

For seven coordinates use the following 42 masks, with repetitions retained:

    19,21,21,25,27,37,37,38,41,41,42,42,43,43,45,45,50,51,53,53,54,
    73,74,74,76,77,82,82,84,84,85,85,86,86,89,90,90,100,102,106,106,108.

Bit c of a mask specifies coordinate c, with coordinate zero the least
significant bit. Every valid partial row extends at least four positions
in this list. `SevenPhaseCapacity.seven_slot_coverage` checks the complete
statement over all 3^7 partial rows by ordinary kernel reduction. It uses
neither `native_decide` nor a trusted external solver.

The supporting list positions for different rows are disjoint, since a
single full word cannot agree with opposite prescribed bits. Consequently
four times the number of rows is at most 42. The number of rows is an
integer, so it is at most ten. The covering lemma and this disjoint-support
counting argument are separately kernel-checked.

## Exact geometric and original conclusions

The resulting strict-cap capacities are 3 at pi/2, 5 at 2*pi/3, and 10 at
3*pi/4. Contraposition supplies an actual triple at or above the respective
threshold in every larger finite injective planar configuration. The finite
strict-cap argument handles degeneracies; no general-position or convexity
hypothesis is present in the exported statements. Configurations of size at
most two are treated directly before constructing the wire graph.

`OriginalSmallCases` handles N=4 using pi/2, N=6..8 using 2*pi/3, and N=11..16
using 3*pi/4. It uses the established first branch for N=5, N=9..10, and
N=17..20, and the direct triangle proof for N=3. The integer-exponent boundary
in the original n=1 formula is preserved. Its final theorem is

    original_lower_three_through_twenty
      {N : Nat} (3 <= N) (N <= 20) : OriginalLowerBound N.

All-N epsilon sharpness and its original superpilot69/ChatGPT 6 Astra and
aznikline attribution remain as recorded in `EXTERNAL_PROOF_ATTRIBUTION.md`.
The first unresolved original cardinality is 21. No all-N solution or prize
submission follows from the present finite cases.

Verification: `verification/small-odd-thresholds-20261105/` records the focused
build, all 53 imported research modules / 940 declarations in the transitive
axiom audit, and compatibility with the existing research umbrella.
