# JSP-000404 — exact-shell rainbow matching capacity (2026-10-14)

## Real structural sharpening

Prior: any genuine same-target NET collision fibre gives a matching
of the candidate lower-/upper-colour slots. The allowed graph can
contain two distinct slot-disjoint edges with the **same** unordered
pair of original flip colours. The already formally proved
`net_collision_canonical_support_fibre_injective` excludes both of
those edges being different REAL same-target sources.

New: introduce the finite maximum **rainbow matching number**
`targetExactShellRainbowMatchingNumber C exponent d`, defined
by admissible edge sets that are pairwise disjoint in BOTH slots AND
pairwise distinct in their unordered transport flip-colour supports.

Actual same-target source fibre F(d) injects into one such matching,
with EXACT preserved size. Therefore, unconditionally:

```text
|F(d)| <= rainbowMatchingNumber(d) <= ordinaryMatchingNumber(d)
E_D <= SUM_(d in actual image) (rainbowMatchingNumber(d)-1)
mobile hard <= singleton + soft + TRUE boolean holes
               + DISTINCT covered diagonals
               + SUM_(d in actual image) (rainbowMatchingNumber(d)-1)
```

This uses actual distinct-support rigidity, not a fictional
AngleCap-derived matching exclusion. The refined graph still only
contains *candidate source-compatible soft bridges*; its edge count,
matching number, colour capacity, and covered diagonals are NOT
themselves literal Boolean holes or unreserved global surplus.

## Proof audit and open goals

- Source: `JSP000404Research/ResidualNetCollisionRainbowMatchingCapacity.lean`.
- Proof route: canonical colour-support fibre injectivity +
  target-exact lower/upper slot injectivity + exact fibre debt identity.
- All added theorems must pass Lean kernel compilation and
  `#print axioms` without `sorryAx` before being certified.
- The unique WIP six-source geometric payment `sorry` remains.
- NEXT: find a genuinely geometric bound/payment for rainbow
  matching components, keeping fifth-centre, twin, mixed-rigid,
  soft and profile loss debts separate.

Verification: [run 38504690545](https://github.com/Charlie-Wang-03/awards/actions/runs/38504690545) PASS, 3,539 jobs; six rainbow capacity theorems only depend on [propext, Classical.choice, Quot.sound].

## No two-edge rainbow obstruction: a weaker local exclusion

At any genuinely hit diagonal d, it suffices to show:
every candidate-edge pair with DISTINCT lower slots and DISTINCT
upper slots has the SAME unordered pair of flip colours.
This permits ordinary two-edge matchings, but excludes all two-edge
*rainbow* matchings.

`ResidualNetCollisionRainbowPairObstruction.lean` certifies:
- all rainbow matching sets are of size ≤1 under this condition;
- the finite rainbow matching number ≤1;
- global actual NET canonical duplicate debt = 0 if the condition
  holds at all actually hit d;
- the literal-hole + distinct-covered-diagonal mobile inequality
  without a duplicate-debt term;
- conversely, positive duplicate debt implies an actual hit target
  graph contains two edges with **disjoint lower slots**, **disjoint
  upper slots** and **DIFFERENT original unordered colour pairs**.

The assumption that all disjoint candidate edge pairs clash in
colour support is still an EXTRA unproved geometry hypothesis:
no AngleCap consequence has been asserted.

Verification: [run 38504957833](https://github.com/Charlie-Wang-03/awards/actions/runs/38504957833) PASS, 3,540 jobs; five rainbow two-edge obstruction theorems only depend on [propext, Classical.choice, Quot.sound]. Both runs compiled the verified umbrella and WIP module; the latter retains the historical sole sorryAx.

## Candidate graph: four original endpoints separated by disjoint colours

The module `ResidualNetCollisionCandidateColourVertexSeparation.lean`
uses the **exact cardinality-one violation shells** already required
for each candidate bridge. For any TWO candidate eligible edges of
the SAME target d, even if neither is known to come from an actual
NET source, DISJOINT unordered flip-colour supports imply all FOUR
cross-edge source bridge endpoints are distinct (lower/lower,
upper/upper, lower/upper and upper/lower).

Conversely, sharing a vertex in ANY endpoint role forces the
candidate edges' original two-colour supports to intersect.

This lifts previously proved four-bit source-only rigidity to the
ENTIRE source-compatible target candidate graph. It narrows the
remaining source-compatible motifs, but does not assert AngleCap
exclusion, global Boolean hole payment, or a lower bound on any
unreserved profile surplus. Lean CI and axiom audit pending.
