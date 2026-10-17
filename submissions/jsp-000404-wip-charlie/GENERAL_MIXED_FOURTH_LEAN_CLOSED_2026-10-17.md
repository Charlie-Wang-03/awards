# JSP-000404 — kernel-checked arbitrary-cardinality mixed fourth-centre exclusion
Date: 2026-10-17
Repository: `Charlie-Wang-03/awards`
Research branch: `research/jsp-000404-sharp-centre`

## Exact status

**CLOSED (Lean kernel, sorry-free):** `JSP000404Research.no_top_mixed_deficitTwo_with_fourth`
in `JSP000404Research/GeneralMixedContradiction.lean`.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39001453178 — SUCCESS,
3,488 Lake build tasks, and `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]`.
The theorem preserves the actual arbitrary-finite planar `AngleCap` setting,
actual centre cycles, exponents `n-1, n-2, n-2`, and support one/two
conditions, plus a distinct fourth actual point. No new unproved hypothesis,
`sorry`, axiom, or modified geometric problem definition is used.

## Short verified proof chain

Let `s,a,b,c` be four distinct actual centres. The true conditions are
`centreExponent(s)=n-1`, `centreExponent(a)=n-2`,
`centreExponent(b)=n-2`, and positive quotient support 1 and 2 at `a,b`.

1. `GeneralMixedBaseAngleLarge.lean`:
   - Generic convex-triangle vertex angular diameter, using genuine
     Euclidean angles.
   - All actual rays at support-two centre `b` lie in
     `conv{s,a,b}` by the independently checked exterior restriction.
   - The true support-two large-angle witness forces
     `angle(s,b,a) >= (n-1)*lambda`.
   - Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39000141390 — SUCCESS,
     no `sorryAx`.
2. `GeneralMixedOtherRaySeparation.lean`:
   - The strict hidden-angle frontier and convex-triangle angle splitting give
     `angle(c,b,a) > delta*lambda`.
   - Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39000350262 — SUCCESS,
     no `sorryAx`.
3. `AnglePath.lean`:
   - Fixes a *mathematical* degeneracy in old draft statements: a path
     containing its angle centre need not have `angle(a,i,a)=0`.
   - Re-proves angular path diameter bounds with the genuine
     `p(z) != p(i)` requirement; for `OtherVertex i` paths this follows
     from injectivity.
4. `SharpPinnedSupportTwoCluster.lean`:
   - Pins the sharp ray in the actual support-two cyclic ray order, excludes
     zero quotient gaps adjacent to it, and uses the exact zero-angle mass
     remainder to bound the entire complementary angular path.
   - Proves `OuterSmallAwayFrom p delta lambda s b`, i.e. for every
     pair of rays `j,k` avoiding `s,b`, `angle(j,b,k) <= delta*lambda`.
   - Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39001398420
     — SUCCESS (3,242 tasks);
     `#print axioms supportTwo_outerSmallAwayFrom_sharp` has only
     `[propext, Classical.choice, Quot.sound]`.
5. `GeneralMixedDiameterObstruction.lean`:
   - Precisely records the immediate contradiction of steps 2 and 4.
   - Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39001307443 — SUCCESS,
     sorry-free.
6. `GeneralMixedContradiction.lean`:
   - Establishes a genuine sharp centre with
     `concrete_unit_deficit_is_sharp`, invokes the unconditional pinned
     support-two cluster theorem, then invokes the already proved diameter
     contradiction.
   - Focused CI 39001453178 SUCCESS, standard-axiom audit above.

## Other verified Lean repairs this iteration

- `PinnedSupportTwoClusterBudget.lean`
- `ThreeCentreTerminal.lean`
- `SixPointMergedOneExceptionCapacity.lean`
- `ResidualThroughLadder.lean`
- `GeneralSharpAvoidsZeroGap.lean`

All five pass in focused CI
https://github.com/Charlie-Wang-03/awards/actions/runs/39000267649.
`DeficitThreeSupportTwoHidden.lean` passes in
https://github.com/Charlie-Wang-03/awards/actions/runs/39000303729.

## What remains OPEN

The complete original JSP-000404 lower-branch dyadic-capacity theorem is
**not proved or disproved**. Its research entry
`PlanarLowerBranchProofAdmittedWIP.lean` still has ONE genuine `sorry`
in the global six-source net, non-reusing defect-payment inequality.
The new mixed-fourth theorem eliminates a genuine geometric subcase;
it does NOT by itself provide a global injective allocation of covered
translation losses, duplicate debt, twin/mixed rigid and soft masses
into OUTSIDE TRUE Boolean holes and genuinely UNRESERVED surplus.
Previously consumed holes/surplus cannot be counted again.

The repository-wide legacy build is not claimed green. Earlier broad
incremental CI (38937218142) failed for unrelated historical modules.
Focused CI success certifies only the named modules and their imports.
Do not promote any conditional equivalence, incomplete Lean root, or
`#print axioms` for the admitted WIP entry to a full solution claim.
