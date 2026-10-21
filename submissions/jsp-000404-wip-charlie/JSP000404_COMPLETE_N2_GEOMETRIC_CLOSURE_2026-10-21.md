# JSP-000404 — Complete n=2 geometric closure checkpoint

Date: 2026-10-21.
Research branch: `research/jsp-000404-sharp-centre`.
**Status: verified proper subcase, not a full solution to JSP-000404.**

## Full actual planar n=2 theorem: kernel PASS

File: `JSP000404Research/PlanarLowerTwoGlobalCapacity.lean`.
Focused [GitHub Actions run #39554707134](https://github.com/Charlie-Wang-03/awards/actions/runs/39554707134):
**SUCCESS**, Lake 3517 jobs; `#print axioms` for both theorems gives
`[propext, Classical.choice, Quot.sound]` and **no `sorryAx`**.

1. `lower_two_original_card_le_four`: under an actual injective finite planar
   `p : V -> Plane`, actual `AngleCap p lam`,
   `t=2+delta`, `0<=delta<1/2`, `lam=pi/t` and actual centre cycles,
   prove `Fintype.card V <= 4`. **No cardinality assumption**.
2. `ProjectionOrdered.planar_lower_branch_n_two_all_centre_dyadic_capacity`:
   under exactly these actual planar lower-branch hypotheses, prove
   `sum_i 2^(centreExponent (cycles i) t) <= 2^2`, for **any**
   finite number of original centres.

### Exact proof chain

- `PlanarLowerTwoAllCentresExposed.lower_two_all_centres_strictlyExposed`:
  `n=2` actual quotient mass ≤2 gives positive support ≤2, which forces
  *every original centre* to be strictly exposed.
- `ExposedSupportIntervalGeneral.exists_supportIntervalCertificate_of_strictlyExposed`:
  each actual strictly exposed centre produces a true support-direction interval
  of length at least `lambda`.
- `SupportIntervalCertificate.turnLength_sum_le_two_pi`:
  those actual intervals from distinct centres occupy disjoint arcs of the
  angle circle, hence `card V * lambda <= 2*pi`.
- With `lambda=pi/(2+delta)` and `delta<1/2`, obtain `card V <=4`.
  In particular, the putative n=2 pentagonal and larger configurations
  are geometrically impossible: this is *not* a conditional cap assumption.
- Existing certified capacity branches handle ≤2 and exactly 3 centres.
  `PlanarLowerTwoFourUnconditionalCapacity.lower_two_four_original_centre_dyadic_capacity`
  handles exactly 4 centres without a no-sharp or no-top additional premise.
- Combine all cases into the new all-cardinality n=2 capacity theorem.

### Main WIP integration

Commit [`76a306335eee80b31279648af48a6c22c8850739`](https://github.com/Charlie-Wang-03/awards/commit/76a306335eee80b31279648af48a6c22c8850739)
replaces the previous `n=2 ∧ card=4` split with a genuinely
unconditional `n=2` branch in
`PlanarLowerBranchProofAdmittedWIP.lean`.
Its branch-specific recompilation remains subject to the three targeted
WIP CI jobs triggered by that commit. This checkpoint does not assert
their success before the corresponding GitHub Actions results.

### Remaining mathematics

The main WIP still contains **exactly one** intentional executable
`sorry`, in the general unrestricted six-source nonreusing actual
Boolean-hole/surplus payment argument. After successful main-WIP
recompilation, that admitted frontier is confined to `n>=3`, outside
the other certified small-cardinality/five-centre geometric branches.
No full proof or counterexample is certified. The independent
original-source closure gate is still OPEN.
Whole-repository Fast Incremental Lean also includes unrelated legacy
source errors, not equivalent to admitted global proof obligations.
