# JSP-000404: additional genuine finite-centre capacity slices and adjacent-gap Lean repair

Date: 2026-10-17
Branch: `research/jsp-000404-sharp-centre`.

## 1. First verified geometric extension (at most five centres)

Lean file: `JSP000404Research/FiveCentreTopNextAtMostOneThirdCapacity.lean`.
Theorems:
* `dyadic_capacity_of_top_next_one_third_two_low`
* `planar_five_centre_top_next_at_most_one_third_capacity`

Under the genuine finite injective planar `AngleCap` hypotheses,
`4 <= Fintype.card V <= 5`, `n >= 4`, `0 <= delta < 1/2`,
`t = n + delta`, `lam = pi / t`, the original actual
`CentreProjectiveCycle` exponents contain a fixed `n-1` centre `s`
and a distinct `n-2` centre `a`. Assume additionally that
at most ONE OTHER centre has exponent `n-3`. The previously proved
`topTwo_tailCount_le_two_of_card_ge_four` is used to rule out
any other `n-1` or `n-2` centre; the remaining at most two
exponents are `<= n-4`.

The exact original dyadic capacity follows from
`2^(n-1) + 2^(n-2) + 2^(n-3) + 2 * 2^(n-4) = 2^n`.
The extra at-most-one-third condition is NOT established for every
planar `AngleCap` configuration.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39028497512
**SUCCESS**, 3502 Lake jobs, both printed axioms exactly
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`.

## 2. Second verified geometric extension (at most SIX centres)

Lean file: `JSP000404Research/SixCentreTopNextNoThirdCapacity.lean`.
Theorems:
* `dyadic_capacity_of_top_next_four_low`
* `planar_six_centre_top_next_no_third_capacity`

Under the same actual `AngleCap` and `n>=4` assumptions,
`4 <= card V <= 6`, a top exponent `n-1` and a distinct
next exponent `n-2`, assume none of the other centres has
exponent `n-3`. Top-two-tail geometric rigidity then forces
every other exponent `<=n-4`. The capacity bound is exact:
`2^(n-1) + 2^(n-2) + 4*2^(n-4) = 2^n`.
The no-third condition is NOT a universal theorem here.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39028793468
**SUCCESS**, 3501 Lake jobs, printed axioms exactly
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`.

## 3. Historical Lean repair (eight diagnostics)

File: `JSP000404Research/AdjacentProjectiveGapIndex.lean`.
The old file contained failing `List.getElem` dependent bounds,
obsolete `List.getElem_mem` explicit argument passing,
and invalid dependent rewriting of the cycle angle list.
Fixes explicitly give valid `getElem` bounds, use the
current `List.getElem_mem` API, and normalize the centre
specialization by `simp` over the provided list decomposition
rather than `rw` with an ill-typed dependent motive.
No original theorem statement was weakened.

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/39028531182
**SUCCESS**, 3213 Lake jobs, all printed interface theorems
with exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## 4. Admitted root narrowing and outstanding global obligation

File: `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`.
Beyond already closed <=4-centre cases and earlier five-centre
no-second case, the admitted root now dispatches:

* five-centre top/next with AT MOST ONE other third-layer centre,
  using the verified stronger theorem above instead of the older
  no-third-only five-centre branch;
* six-centre top/next with NO other third-layer centre.

Only the complement flows to the original actual-edge six-source
external TRUE-hole payment, with exactly ONE deliberate executable
`sorry` in the WIP. This *narrows the quantified sorry domain*
but DOES NOT close that payment or prove/disprove the original
unrestricted JSP-000404.

Main WIP specialized verification launched:
https://github.com/Charlie-Wang-03/awards/actions/runs/39028964777
and sibling frontiers at #39028964739 and #39028964748.
At the point this report was drafted their latest actual conclusion
was NOT YET AVAILABLE. Verify before citing as successful.

## 5. Full build reality

Most recently observed completed Fast Incremental Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/39027392586
failed with 258 reported Lean diagnostics across historical modules.
The repaired adjacent gap interface removes its targeted historical
errors, but broad root success cannot be assumed; re-count only
after the latest full run finishes.

The one admitted global debt remains the ACTUAL nonreusable payment
of mobile, soft, twin, mixed, certified NET duplicate, projected
profile, and covered-blocker liabilities into TRUE external holes
and GENUINELY unreserved surplus. The kernel-checked conditional
finite-cardinality slices above do not establish this general
allocation.

No admitted proof hole other than the pre-existing single WIP
`sorry` was intentionally created. No new axioms are used.
