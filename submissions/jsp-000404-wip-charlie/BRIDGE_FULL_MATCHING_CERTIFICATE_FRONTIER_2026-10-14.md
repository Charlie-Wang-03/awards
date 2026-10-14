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
