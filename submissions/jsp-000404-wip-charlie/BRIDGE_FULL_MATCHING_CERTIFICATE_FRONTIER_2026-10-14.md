# JSP-000404 — Exact finite matching certificate frontier

Date: 2026-10-14. Research only, no complete proof claim.

## New mathematical necessary condition

For EVERY target diagonal d, all ACTUAL NET sources selecting d
embed into the target-exact allowable bipartite slot graph as a
finite matching M(d) of **exactly the same cardinality**.

This upgrades the previous two-source / two-edge obstruction to
arbitrary source fibre size, using distinct original lower/reverse
and upper/forward colour slots. A fibre of k sources forces a
matching of size k, not merely a set of k candidate edges.

As a consequence, any verified upper bound on the size of
matchings in that particular eligible graph bounds its TRUE
source-fibre size and the exact duplicate debt
  E_D = sum over hit d of (|F_d| - 1).
This is a matching-certificate reduction, NOT a new unconditional
upper bound derived from planar AngleCap. Without a geometric
matching restriction it does not improve the global numerical bound.

## Proof hygiene

- Lean module: `ResidualNetCollisionFullMatchingCertificate.lean`
- Source inputs: genuine NET source fibres and fixed-diagonal
  lower-/upper-colour slot injectivity, with target-exact
  bridge eligibility.
- Source to candidate edge is assembled using actual forward
  and reverse transport provenance, NOT arbitrary graph edges.
- No double use of candidate slot capacity, covered sinks or
  TRUE Boolean holes is claimed.
- The research-only six-source payment `sorry` is unchanged.

Validation: pending fast incremental Lean run on branch HEAD;
record the exact run and axiom outcome before asserting PASS.

## Remaining hardest geometric task

Prove some **quantitative** matching restriction from actual
AngleCap / source-native cross-bridge geometry, or assign
nonoverlapping certified resources to each irreducible matching
edge, while also paying covered-target, twin, mixed-rigid, soft
and projected-loss debts.

## Follow-up: explicit finite maximum-matching invariant

The `ResidualNetCollisionMaximumMatchingPayment.lean` module defines
`targetExactShellSlotMatchingNumber C exponent d` as the **maximum
size of a finite slot matching** in the candidate graph, not as a
previously assumed bound. This is a finite but potentially costly
combinatorial definition. The resulting statements are unconditional:

```text
|true source fibre F_d| <= matchingNumber(G_d)
E_D <= sum_(d in true target image) (matchingNumber(G_d) - 1)
mobileHard <= singleton + soft + trueHoles + coveredDiagonals
             + sum_(d in true target image) (matchingNumber(G_d) - 1)
```

The cardinal `matchingNumber(G_d)` is a count of source-compatible
candidate edges, **not** a newly available hole/surplus budget.
No general upper bound from AngleCap or complete six-source payment
follows from this replacement. Lean CI evidence is pending.


## Tightening the candidate edge graph (2026-10-14)

Source audit exposed two **missing local eligibility filters** in
the graph used for matching-number certificates. Its original
candidate edges were constrained by source-compatible bridges
and *opposite* endpoint violation colours, but did not explicitly
require the colour in each pair to be **retained-inactive at its own
endpoint**. The revised graph now enforces BOTH own-endpoint
conditions in addition to the original source-compatible bridge
and two exact opposite-endpoint target-violation conditions.

The actual-source edge theorem is repaired with the previously
certified `strictDescentRigidPairColor_spec` and
`transportablePairColor_spec` inactivity lemmas. No genuine
NET source is discarded. A new theorem
`target_exact_shell_edge_endpoints_mem_exact_colour_slots`
certifies EVERY candidate edge's endpoints belong to the
existing exact lower and upper colour-slot pools.

This strictly **tightens the admissible graph definition in
principle** (no strictness witness asserted for all configurations).
Its maximum-matching number may become smaller, strengthening
the unconditional source-fibre and duplicate-debt bound. It is
not a proof that these matching credits are TRUE Boolean holes.
Isolated module: [GitHub Actions run 38503265973](https://github.com/Charlie-Wang-03/awards/actions/runs/38503265973) — PASS, 3,270 jobs; actual-source edge inclusion and new endpoint membership theorem have only standard `[propext, Classical.choice, Quot.sound]` axioms. Full import-chain replay: [GitHub Actions run 38503488740](https://github.com/Charlie-Wang-03/awards/actions/runs/38503488740) — PASS, 3,538 jobs, both `VerifiedOverlapRewire` and `PlanarLowerBranchProofAdmittedWIP` compiled after the tighter edge-predicate change. `VerifiedOverlapRewire` stays sorry-free. The WIP theorem still intentionally reports exactly the historical `sorryAx`; it does NOT close the global payment.
