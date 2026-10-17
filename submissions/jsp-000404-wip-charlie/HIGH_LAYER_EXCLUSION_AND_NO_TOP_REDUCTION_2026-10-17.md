# JSP-000404 — closed high-layer planar profile and no-top support reduction
Date: 2026-10-17
Repository: `Charlie-Wang-03/awards`
Branch: `research/jsp-000404-sharp-centre`

## 1. Exact proof state

**The original JSP-000404 lower-branch global dyadic-capacity theorem remains OPEN.**
The only executable `sorry` in the research root
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` is unchanged.
It represents a genuine six-source net defect-payment inequality, which
must pay all debts with *outside TRUE holes* and genuinely *UNRESERVED*
dyadic surplus, without reuse. The new high-layer restrictions DO NOT
establish that payment. No full proof or disproof is claimed.

All the focused Lean modules listed below passed their specific CI checks
and their exported new target theorems have no `sorryAx`
(only `propext`, `Classical.choice`, `Quot.sound`).
These checks do not assert that the entire historical broad incremental
build is green.

## 2. Actual top plus two next centres: full four-case closure

`JSP000404Research/NoTopTwoNextMultiplicity.lean`

- `actual_deficit_two_support_one_or_two`: genuine exponent `n-2`
  centres have quotient support 1 or 2 for `n>=3`.
- `no_top_and_two_next_with_fourth`: with four distinct centres
  `s,a,b,c`, under original injective planar `AngleCap` with
  `n>=3, 0<=delta<1/2, t=n+delta, lambda=pi/t`, the pattern
  `k(s)=n-1`, `k(a)=k(b)=n-2` is impossible.
- Cases support 1/1 (already certified transition packing), 1/2, 2/1
  (genuine arbitrary-finite mixed exclusion, closed on 2026-10-17)
  and 2/2 (repaired pinned sharp support-two multiplicity) are all
  individually closed, not conditionally assumed.
- CI https://github.com/Charlie-Wang-03/awards/actions/runs/39003986015
  **SUCCESS**, 3,490 tasks, target axioms
  `[propext, Classical.choice, Quot.sound]`.

`JSP000404Research/SharpSupportTwoMultiplicity.lean` was repaired in this
chain and `no_two_supportTwo_deficitTwo_around_sharp` has the same
sorry-free axiom audit in the CI above.

## 3. Global high-layer count, not merely a selected triple

`JSP000404Research/TopForcesNextMultiplicity.lean`

- `exists_fourth_of_card_ge_four`: rigorous cardinality witness.
- `actual_next_exponent_card_le_one_of_top`: with at least four
  actual centres, if an exponent `n-1` centre exists, the *global*
  number of exponent `n-2` centres is at most one.
- CI https://github.com/Charlie-Wang-03/awards/actions/runs/39004055291
  **SUCCESS**, 3,491 tasks, sorry-free axiom audit.

`JSP000404Research/GenericTopExponentMultiplicity.lean` was
separately repaired and proves top exponent multiplicity at most one
for at least three centres (with `n>=2`).
CI https://github.com/Charlie-Wang-03/awards/actions/runs/39003906410
**SUCCESS**, sorry-free.

`JSP000404Research/ProjectionTopForcesNextMultiplicity.lean`

- `ProjectionOrdered.projection_top_forces_next_card_le_one` transfers
  the same NEXT layer restriction to the exact
  `ProjectionOrdered V` / `reindexedPoint` index used by the original
  six-source planar root, without introducing a surrogate graph.
- CI https://github.com/Charlie-Wang-03/awards/actions/runs/39004200185
  **SUCCESS**, 3,495 jobs, sorry-free.

This is a genuine improvement in the top-layer configuration space;
it does not yet give a non-reusing global matching from debt events to
unreserved eligible payment resources.

## 4. No-top complement: support-one multiplicity restriction

`JSP000404Research/SecondLayerNoTopReduction.lean`

- `no_three_supportOne_secondLayer_of_four_le_n`:
  for `n>=4`, three different exponent `n-2` centres cannot all
  have quotient support one; transition quotient `n-1` paid three
  times would exceed the verified three-centre packing bound `2*n`.
- `four_secondLayer_has_two_supportTwo`: any four different
  exponent `n-2` centres contain two support-two centres.
- CI https://github.com/Charlie-Wang-03/awards/actions/runs/39004340685
  **SUCCESS**, 3,491 tasks, `#print axioms` both sorry-free.
- This is a **reduction, not an exclusion**, of the surviving no-top
  support-two geometry.

## 5. Additional actual Lean repairs

- `AdjacentZeroGapActualAngle.lean`: removes Lean reserved identifier
  `prefix`, fixes angle-cap binder scoping and positive scale;
  establishes zero-gap small angle and sharp-ray avoidance.
  CI https://github.com/Charlie-Wang-03/awards/actions/runs/39003789215
  **SUCCESS**, 3,235 tasks, sorry-free.
- `FourCentreSharpReduction.lean`: restores legacy theorem using
  the stronger *full* exclusion. The old mixed-only disjunction is now
  logically vacuous and its header explains that.
  CI https://github.com/Charlie-Wang-03/awards/actions/runs/39004277694
  **SUCCESS**, 3,491 tasks, sorry-free.
- The earlier 2026-10-17 closure of
  `GeneralMixedContradiction.lean` remains established by CI
  https://github.com/Charlie-Wang-03/awards/actions/runs/39001453178
  **SUCCESS**, 3,488 jobs, sorry-free.

## 6. Remaining mathematically substantive targets

The resulting branch decomposition is sharper:

- If `n>=3`, `card V>=4`, and a TOP `n-1` centre exists:
  at most one second-layer `n-2` centre exists.
- In the no-top regime, for `n>=4`, any four `n-2` centres force
  two support-two centres. Their actual geometric coexistence and
  contribution to global payment remain open in general.
- For all regimes, the exact global outstanding inequality remains
  *six-source debt* ≤ *outside TRUE holes* + *genuinely UNRESERVED
  surplus*, with actual source/blocker/flip ownership, duplicate hits
  and all prior reservations respected.
- No reported cardinality argument alone converts a COVERED bridge
  sink, local diagonal, or already reserved strict lower shell into an
  eligible credit.
- There are still older Lean compilation failures outside these
  focused modules; the previous broad incremental run
  https://github.com/Charlie-Wang-03/awards/actions/runs/39001440008
  failed and is not overridden by these focused successes.

Do not merge the research WIP to the upstream prize submission or
claim the full question solved on the strength of these structural
subcase theorems.
