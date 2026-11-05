# The nine-phase capacity and the original cases through forty

This is a complete proof of family B at n=4, not of family B for arbitrary n.
For every finite injective planar configuration, a strict angle cap of 4*pi/5
implies cardinality at most twenty. Together with the previously proved first
family and small cases, this proves every original lower bound for 3<=N<=40.
The first unresolved cardinality is N=41. All-N epsilon sharpness retains the
external attribution recorded in `EXTERNAL_PROOF_ATTRIBUTION.md`.

## From actual geometry to ordered integer pair times

The existing actual-point construction supplies projection wires, their
sorted crossing directions, and a forward angle lift. The continuous wire
argument proves that every simple directed cycle has winding one or two.
Because the finite configuration has a strict angle cap, there is uniform
positive slack; its normalized width is strictly below five. The previously
proved half-grid retiming theorem therefore supplies integer doubled times H
at period nine. Consecutive events on a wire are nondecreasing and have gap
at least two when their signs differ. The reflected closing constraint gives
the analogous cyclic inequality.

Consequently, for any two events incident to the same vertex, their times
differ in absolute value by at most nine. Equal signs strengthen this to
seven; opposite signs require a gap of at least two. These are consequences
of the full consecutive and closing constraints, not extra assumptions.

Retiming also preserves the original triple order. If a<b<c in the original
projection order, the original direction of pair ac lies between those of
ab and bc. Each comparison is between two events sharing a wire. Since H
is nondecreasing on each sorted wire, the same betweenness holds for H.
`OrderedNinePhase` proves this directly, including weak equalities.

## Signed rows and coherent pair phases

Reduce every incident event time modulo nine. Its row bit is the existing
alternating `OddWire.eventBit` of its integer time and endpoint sign. The
local gap inequalities ensure consistency at repeated residues and prohibit
equal occupied bits at adjacent cyclic positions. Thus every vertex gives a
proper partial two-colouring of C9. At their shared pair event, two vertices
have opposite bits. Every pair is therefore separated.

The reduction preserves more than pair separation. At a shared phase c,
compare the first row bit with the parity bit `decide (c % 2 = 0)` to recover
the pair's order relative to the cut. For a triple, these three comparisons
are transitive; in their resulting vertex order the middle pair phase lies
between the other two. This is the predicate `OrderedPhases`. The integer
arithmetic theorem in `NinePhaseOrder` derives it from original betweenness
and the signed gap bounds. `NinePhaseSchedule` handles all permutations.
This coherent pair-phase structure is retained when rows are extended.

## A finite cover first bounds the capacity by twenty-one

Every proper partial C9 row extends a maximal proper row. There are exactly
78 maximal rows: 18 with one hole and 60 with three holes. The catalog used
in Lean lists independent odd hole sets in increasing mask order, with
alternating occupied bits in both polarities. `catalog_completion` checks
extension for every one of the 3^9 partial assignments by kernel reduction.

Use the following 42 binary words, with bit c representing coordinate c:

```
73 83 85 101 107 146 149 153 165 166 169 170 171 173
179 181 202 205 213 214 219 292 297 298 306 309 330
332 338 340 341 342 345 346 358 362 365 404 410 426 428 438
```

Every catalog row agrees with exactly two of these words. Separated rows
have disjoint compatible-word supports, so a family has at most 21 rows.
If it has 21, all 42 words must be covered. Row extension preserves the
original shared phases, row bits at those phases, and triple coherence.

## Saturation forces an incoherent five-row core

The finite saturation certificate says that a pairwise-separated catalog
family covering all 42 words contains one of the following two cores. One
has positive/negative bit masks

```
(292,146) (69,274) (41,148) (328,162) (73,292)
```

and the other swaps both masks in every row. The proof uses Boolean
variables for the 60 three-hole rows: 24 cover clauses, 384 incompatible-pair
clauses, and two clauses excluding the cores. An explicit case-split and
unit-propagation proof refutes their conjunction. It has 99 search nodes
and uses 336 of the 410 clauses. The generated Lean proof contains only
Boolean cases and equality rewrites. The semantic wrapper checks each
numeric cover/conflict fact against the concrete row data in the kernel.
No external SAT result or proof-reflection axiom is assumed.

Neither core admits coherent shared phases. Number its rows 0,...,4. Their
opposite common coordinates force

```
t01=8, t02=2, t03=5, t14=2, t24=5, t34=8,
t04 in {2,5,8}.
```

Triangle 014 excludes t04=5, triangle 024 excludes t04=8, and triangle 034
excludes t04=2. This exhausts the possible common phases. Global bit reversal
has the same obstruction. `NinePhaseFiveRowObstruction` checks these exact
phase domains and the three order contradictions. Therefore saturation is
impossible, and every coherent row family has cardinality at most twenty.

## Formal scope and independent checks

`planar_card_le_twenty_of_strict_angles` combines this capacity with the
actual geometric construction. Its hypotheses are only injectivity and the
strict original angle bound. Empty/small finite types and all geometric
degeneracies are covered. Contraposition gives `planar_four_fifths_angle`.
`original_lower_three_through_forty` matches the exact alphaN formula,
including its dyadic endpoints and first/second-branch boundaries.

The focused build has 3,272 jobs. A transitive audit covers 64 imported
research modules and 1,088 declarations, including private declarations,
with no axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
The Boolean contradiction and five-row obstruction themselves use only
`propext`. The updated umbrella file also compiles.

An independent Python standard-library checker enumerates all 19,683
partial assignments and their 2,785 proper members, verifies the catalog
and cover, and explores all saturation families in 327 search nodes. It
finds exactly four families, each containing one of the two excluded cores.
This classification is corroborating evidence; the Lean proof does not
assume it. Evidence and commands are in
`verification/nine-phase-threshold-20261105/`.

General family B for n>=5 remains open. The 21-row local-model obstruction
has now been excluded by genuine triple coherence, without assuming that
arbitrary partial-row families come from geometry. A general capacity or
an appropriate retiming-and-reduction theorem is still required.
