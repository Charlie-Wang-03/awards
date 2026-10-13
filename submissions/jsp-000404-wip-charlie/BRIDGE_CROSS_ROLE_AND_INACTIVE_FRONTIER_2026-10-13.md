# JSP-000404: Cross-role endpoint obstruction and inactive-cube frontier

Status: **LOCAL STRUCTURE VERIFIED / GLOBAL SIX-SOURCE PAYMENT OPEN**.

Branch: `research/jsp-000404-sharp-centre`. This note follows
`BRIDGE_STRICT_LOWER_GAP_PROOF_FRONTIER_2026-10-12.md` without
replacing its full global six-source payment statement.

## Three verified sorry-free Lean modules

1. `JSP000404Research/ResidualNetCollisionCrossRoleEndpointSeparation.lean`
   proves four local theorems: actual NET collisions hitting the same
   diagonal with a cross-role shared endpoint force the corresponding
   original forward/reverse flip colours to coincide; every original
   bridge has distinct endpoints; and any Hamming-4 same-target source
   pair must have **four pairwise distinct original soft bridge vertices**
   (all six pairwise inequalities, including cross-role).
   Fast Lean CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38425922249
   PASS, 3262 build jobs, no `sorryAx` in the four new declarations.

2. `JSP000404Research/ResidualNetCollisionSharedVertexTwoBitClassification.lean`
   proves that any two DISTINCT genuine NET sources with the same
   certified canonical diagonal whose original bridges share a vertex
   in **any** endpoint role have Hamming distance exactly TWO; their
   original unordered forward/reverse flip-colour pairs intersect
   in exactly ONE colour.
   Fast Lean CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38426755573
   PASS, 3263 build jobs, no `sorryAx`.
   Two real Lean compiler errors were repaired: non-existent
   `Finset.not_mem_empty`, and a local Hamming-cardinality let alias
   that had not been unfolded for `omega`.

3. `JSP000404Research/ResidualNetCollisionSharedVertexInactiveCapacity.lean`
   proves three local theorems: (i) disagreement support of two
   completion words inside a fixed retained cube lies within the
   centre's inactive Boolean coordinates; (ii) every genuine NET
   collision sink lies in both original soft bridge endpoint cubes;
   (iii) two distinct same-target NET sources sharing a bridge
   endpoint `c` require **at least TWO inactive Boolean coordinates at c**.
   Fast Lean CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38427616056
   PASS, 3264 build jobs, no `sorryAx`.

## Precise local classification

Write `D(s)` for the canonical source-certified double-flip diagonal,
`B(s)=(b_s,v_s)` for the actual original source bridge, and `A_s`
for the unordered pair of its two original distinct flip colours.

For genuine NET sources `s != t` with `D(s)=D(t)`:

```text
Hamming(s,t) = 4
  ==> b_s, v_s, b_t, v_t are pairwise distinct.

Any endpoint (same-role or cross-role) of B(s)
  equals an endpoint of B(t)
  ==> Hamming(s,t) = 2, |A_s ∩ A_t| = 1.

If shared vertex c exists in the second case,
  ==> card(Finset.univ \ retainedActive(C,c)) >= 2.
```

In particular, a centre with inactive completion dimension at most
one cannot be a shared vertex of a nontrivial duplicated-diagonal
genuine source pair. This eliminates a concrete low-dimensional class,
but **does not** eliminate all 2-bit duplicate motifs and does not
follow globally from the current AngleCap axioms.

These local results are now imported into the independent
`VerifiedOverlapRewire.lean` and the separate admitted
`PlanarLowerBranchProofAdmittedWIP.lean`.

## Remaining actual mathematical obligation

The single intentionally admitted WIP `sorry` remains the real
geometric six-source non-reuse payment: soft overlap, net movable
forward and reverse hard masses, terminal twin, ascending/descending
mixed rigid debts, and projected loss must be bounded using ONLY
literal global Boolean holes and genuinely unreserved profile surplus.
Existing covered soft-bridge cubes are NOT holes; dimension-gap budget
is NOT automatically unreserved surplus.

Remaining possible duplicate-target motifs include:
- 4-bit sources from four pairwise distinct soft bridge centres;
- 2-bit sources from different bridges, including fully
  vertex-disjoint pairs or shared vertices with at least two
  inactive coordinates;
- opposite diagonal coverage by source blockers or fifth centres.

No formal or mathematical completion of JSP-000404 is claimed.
