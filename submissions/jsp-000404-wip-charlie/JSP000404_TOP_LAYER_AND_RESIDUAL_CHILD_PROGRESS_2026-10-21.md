# JSP-000404 | Planar top-layer rigidity and residual-child Lean repairs

Research branch: `research/jsp-000404-sharp-centre`. Date: 2026-10-21.
**Factual research checkpoint; NOT a full proof or disproof.**

## 1. Proven original planar low-parameter closure (pre-existing on arrival)

At HEAD `d9ff1df81e65761aaaae52d39c96b3358ac1c470`, the original
`PlanarLowerBranchProofAdmittedWIP.lean` explicitly discharged ALL genuine
`n=1` and `n=2` AngleCap subcases, and all configurations with at most
four original projected centres. The real source geometry,
`PlanarLowerTwoGlobalCapacity.lean`, uses exposed support-arc packing
to bound the original cardinality by four when n=2, then the fully
verified quadrilateral geometry to establish its exact dyadic bound.

Both original WIP checks [#39555487338](https://github.com/Charlie-Wang-03/awards/actions/runs/39555487338)
and [#39555487152](https://github.com/Charlie-Wang-03/awards/actions/runs/39555487152)
reported SUCCESS, still allowing exactly one intentional root `sorry`.
The sole residual therefore starts at `n>=3`, `card V>=5`.

## 2. New actual planar exponent-multiplicity obstruction

`PlanarUniqueTopExponent.lean` composes already-certified geometry:
- `concrete_unit_deficit_is_sharp`: actual exponent n-1 implies
  `SharpAt p delta lam s`.
- `two_sharp_no_third_small_delta`: under real AngleCap and
  `delta<1/2`, two different sharp centres with a third different
  vertex are impossible.
- `no_top_and_two_next_with_fourth`: one actual exponent n-1 and two
  different exponent n-2 centres cannot coexist with a fourth point.

New resulting theorems:
`no_two_top_exponents_with_third`,
`top_exponent_unique_of_card_ge_three`,
`no_two_next_exponents_beside_top_of_card_ge_four`.

Verified [focused CI #39567011440](https://github.com/Charlie-Wang-03/awards/actions/runs/39567011440):
**SUCCESS**, 3491 Lake jobs; each printed theorem axioms
`[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

On the genuine main root WIP, commit
[`103d31b459381213afa31b4115d713f9dab534e0`](https://github.com/Charlie-Wang-03/awards/commit/103d31b459381213afa31b4115d713f9dab534e0)
imports the file and proves `hTopUnique` and `hTopNextUnique`
INSIDE the original `n>=3`, `card V>=5` residual branch.

These facts constrain the admitted region but do not themselves provide
the missing global non-reused six-source payment. The root still has
exactly ONE intentional executable `sorry` (line 900 in that commit).
The two focused WIP checks were still running when this checkpoint was
written; do not count them as passed without verifying their conclusions.

Additional census-form theorem declarations,
`actual_top_exponent_layer_card_le_one` and
`actual_next_exponent_layer_card_le_one_of_top`, were committed after
the first PASS. Their own CI is pending; their kernel status must be
checked separately from the previously certified witness lemmas.

### First unresolved n=3, five-centre shapes (deduced classification)

For `n=3`, `card V=5`, all true exponents are in `{0,1,2}`.
By proven top/next uniqueness, the only potentially unclosed high-weight
shapes, after applying the existing five-centre top/no-next theorem and
the existing no-top `card + count_next <= 8` capacity terminal, are:

- no exponent 2, with **at least four exponent-1 centres**; or
- exactly one exponent-2 centre and **exactly one exponent-1 centre**.

This is a straightforward arithmetic reduction of the applicable
existing theorems, not an independently kernel-checked equivalence
module and not an exclusion of either remaining geometric pattern.
The second case has dyadic sum `4+2+1+1+1=9>8` if realizable;
the first also exceeds eight. Either needs a TRUE planar AngleCap
impossibility proof (or a rigorously certified counterexample).

## 3. Historical Lean compiler repair, independently verified

The old `ResidualChildColoring.lean` originally emitted about thirty
diagnostics in the full-tree incremental workflow. We restored the
classically induced `LinearOrder` for both residual subtype vertex
sets, proved the missing
`residualCoord_mem_active_of_isResidual` from actual residual-edge
activity at BOTH endpoints, repaired four mismatched colour-equality
orientations, and retained true high-source/high-sink witnesses during
child exponent estimates.

[Focused CI #39567236865](https://github.com/Charlie-Wang-03/awards/actions/runs/39567236865):
**SUCCESS**, 3116 Lake jobs. This does NOT make the entire historical
full-tree incremental workflow green: other modules still have errors.
No theorem or payment assumption was weakened to repair the errors.

## 4. Remaining full JSP-000404 research frontier

The global admitted `sorry` still concerns true planar six-source
non-reusing payment: actual outside TRUE Boolean holes, genuinely
unreserved dyadic surplus, covered-loss carriers, twin/rigid/mixed
obligations, NET duplicate debt and cross-coordinate collisions.
Explicitly deriving unique high-weight exponent centres helps prevent
overweight profiles but does NOT pay these global liabilities.

The historical source-closure gate is separately OPEN. Do not claim
the original JSP-000404 has been proved or disproved.

Immediate continuation: verify the two focused WIP checks and the
new cardinality-census theorem CI, repair any actual Lean errors,
then attack the two n=3/five-centre geometric motifs above, while
retaining global all-n six-source accounting as the final gate.
