# JSP-000404 — general fourth-layer tradeoff and legacy deletion repairs

Date: 2026-10-17. Branch: `research/jsp-000404-sharp-centre`.
Factual checkpoint. **No claim of a complete original proof/disproof.**

## Baseline audited

Previous three main WIP CI checks for the top-inclusive
three-layer capacity and later nine-centre slice all succeeded:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39042018472
- https://github.com/Charlie-Wang-03/awards/actions/runs/39042018468
- https://github.com/Charlie-Wang-03/awards/actions/runs/39042018515

Prior optional whole-tree Fast Incremental Lean:
https://github.com/Charlie-Wang-03/awards/actions/runs/39042534322
FAILED with **227 historical Lean diagnostics**, not 227 mathematical
open obligations. At baseline the sole admitted mathematical hole
was `PlanarLowerBranchProofAdmittedWIP.lean` line 822
(only executable `sorry` in the allowed WIP proof).

A separate genuinely geometric nine-centre necessary fork,
`planar_nine_overweight_support_two_three_or_six_fourth`,
was independently kernel-verified:
https://github.com/Charlie-Wang-03/awards/actions/runs/39042547507
SUCCESS.

## Certified historical MaxStableCentre repair

`JSP000404Research/MaxStableCentre.lean` failed to synthesize
`DecidableEq V` in two deletion-bonus theorems.
Added the typeclass parameter in the relevant existing generic
signatures (without modifying their mathematical conclusions).

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39044614169
**SUCCESS**, 3097 Lake jobs. All three printed theorem axioms:
`[propext, Classical.choice, Quot.sound]`. No new `sorryAx`.
The two historical file errors were removed.

## New general true-planar fourth-layer capacity

`JSP000404Research/TopFourthLayerCardinalityTradeCapacity.lean`
proves, under genuine injective planar `AngleCap` geometry,
`n>=5`, `0<=delta<1/2`, `t=n+delta`,
`lam=pi/t`, a true exponent `n-1` centre,
no `n-2` centres, and every `n-3` centre having
actual positive quotient support exactly 1:

If
`card V + card {i | centreExponent(C i,t)=n-4} <= 14`,
then the full genuine dyadic capacity
`sum_i 2^centreExponent(C i,t) <= 2^n` follows.

Proof:
- true planar top uniqueness: exactly one top centre (for |V|>=3);
- true planar sharp-centre exclusion of two distinct third-layer
  support-one centres: count <=1;
- true exponent bound `centreExponent<n`;
- existing kernel-proved four-layer dyadic census:
  `sum_i 2^k <= (m+15*r1+7*r2+3*r3+r4)*2^(n-5)`.
  Thus <=`(m+18+r4)*2^(n-5) <=2^n`.

Unlike the older `<=9 centres, <=5 fourth-layer` slice,
THIS has **no fixed upper bound** on the total centre cardinality.
The `m+r4<=14` census is still an explicit additional condition,
NOT shown to follow universally from `AngleCap`.

It also proves the exact necessary obstruction:
if overweight persists under the same support-one hypotheses,
`m+r4>14`.

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39044731454:
**SUCCESS**, 3510 Lake jobs. Both printed axioms exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

Root integration commit
`a0d51cdbabaf04cccb52cad7953e2d39888bb4b6`:
the earlier fixed nine-centre case was REPLACED by this broader
general slice in `PlanarLowerBranchProofAdmittedWIP.lean`.
The sole original executable `sorry` remains (around line 821
after replacement). Its branch excludes the stronger profile family.

Main WIP root focused integration runs at this exact SHA:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39045076709
- https://github.com/Charlie-Wang-03/awards/actions/runs/39045076671
- https://github.com/Charlie-Wang-03/awards/actions/runs/39045076657

**At first drafting these were not yet concluded.** A successful
standalone mathematical file does NOT certify the root integration.

## Further genuine overweight necessary fork

The same new module subsequently adds
`planar_top_no_next_overweight_support_two_three_or_fourth_trade_excess`.
There is no `card V<=9` premise. Given a true top and absent next
layer, ANY original overweight configuration must satisfy
EITHER a genuine `n-3` centre of quotient support 2 or 3,
OR `m+r4>=15`. The proof uses the independently verified
`concrete_deficit_three_structure` classification and the
general capacity theorem above, without asserting the existence
of an overweight configuration.

New focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39045139179
was still in progress when drafted. Check `#print axioms`.

## Historical SecondDeletionSlack repair progress

`JSP000404Research/SecondDeletionSlack.lean` originally had
19 historical diagnostics, largely cascading from an absent
explicit import for the now independent
`UnitGainDeletionBonus.lean` declaration. Import added.

First dedicated CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39044782770
failed with only two source-level errors:
- distribution of the oldDeletionWeight sum before unfolding;
- missing `DecidableEq V` instance for a two-element `Finset`.

Both were repaired by moving the unfold ahead of
`Finset.sum_add_distrib` and introducing `classical` in
the distinct-survivor proof. Source commit:
`661ff4153b58956876b60b61d9d9250a0e7cfd3e`.
Second dedicated CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39044945632
was in progress when drafted. No success assumed yet.

## Sole genuine unresolved theorem

The main goal still requires an unconditional **six-source,
nonreusable actual-edge payment**. Hard, soft, mobile, twin,
mixed, NET duplicate, blocker and projected-loss debts must
be simultaneously covered by **actual external TRUE holes**
and **genuinely unreserved dyadic surplus**, with no reuse.
None of the conditional dyadic subcases or necessary overweight
forks above proves this unrestricted geometric payment. No actual
counterexample to JSP-000404 was certified.
