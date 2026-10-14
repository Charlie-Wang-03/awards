# JSP-000404 — Exact-slot two-edge matching obstruction (2026-10-14)

This is **research-only**. It does not establish a global planar AngleCap
matching-exclusion theorem, or settle the original Sendov/Blumenthal problem.

## Exact obstruction

Let E(d) be the candidate graph of genuine-source-compatible, target-exact
double-shell bridge / flip-colour slot edges at diagonal d. Earlier kernel
proofs show that each actual NET collision source selects E(d), and
that either original endpoint-colour slot determines the source uniquely
when d is fixed.

Therefore a target fibre containing **two distinct actual sources**
forces **two edges of E(d) disjoint on BOTH slot sides**. Equivalently,
if any two candidate edges of E(d) share a lower OR an upper slot,
the actual fibre has at most one source.

This criterion is strictly weaker than requiring |E(d)| <= 1:
a star with arbitrarily many edges still has no two disjoint edges.

For all actually hit target diagonals, a verified no-disjoint-edge
hypothesis gives E_D=0 and removes the explicit source-duplicate
term from the already certified *mobile* accounting inequality.
It does NOT pay the distinct covered-diagonal, terminal twin,
mixed-rigid, soft overlap, or projected profile-loss terms.

## Lean module and verification

- Module: `JSP000404Research/ResidualNetCollisionMatchingObstruction.lean`
- Four claims: target fibre <=1; two-disjoint-slot-edge necessary
  witness; global duplicate debt zero conditional on matching-free
  candidate graphs; mobile ledger with duplicate debt eliminated.
- Dependencies: the previously certified exact-shell bipartite cover
  and true-hole/covered-diagonal mobile ledger.
- Lean/Mathlib: use repository-pinned versions.
- Build and axiom evidence must be checked on this branch's CI;
  no green status is asserted before the checks finish.

## Open mathematical gate

Prove a matching exclusion or a quantitatively paid matching bound
from **actual** planar AngleCap geometry, without treating covered
soft edges, target slots, or previously reserved surplus as TRUE
Boolean holes or free resources. The sole global six-source WIP
`sorry` remains unchanged.
