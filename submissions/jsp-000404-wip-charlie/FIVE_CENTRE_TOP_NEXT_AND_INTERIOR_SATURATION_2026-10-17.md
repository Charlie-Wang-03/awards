# JSP-000404 — Genuine top/next five-centre branch and interior saturation repair

Date: 2026-10-17
Branch: `research/jsp-000404-sharp-centre`.
Scope: kernel-verified local mathematics and Lean compatibility repair; **not a full solution**.

## 1. Newly closed actual planar five-centre subcase

`JSP000404Research/FiveCentreTopNextNoThirdCapacity.lean` proves two theorems without `sorryAx`.

- `dyadic_capacity_of_top_next_three_low`: for an arbitrary finite exponent
  profile on at most five vertices with `n >= 4`, one fixed `n-1`
  exponent, a distinct fixed `n-2` exponent, and every other exponent
  `<= n-4`, the exact dyadic capacity `sum 2^k <= 2^n` holds.
  The dyadic budget is `8+4+3 <= 16` times `2^(n-4)`.
- `planar_five_centre_top_next_no_third_capacity`: genuine finite
  injective planar `AngleCap p lam`, `4 <= card V <= 5`,
  `n >= 4`, `0 <= delta < 1/2`, `t = n + delta`,
  `lam = pi/t`, and actual `CentreProjectiveCycle` data.
  A fixed top centre `s` has exponent `n-1`, a distinct
  next-to-top centre `a` has exponent `n-2`, and no **other**
  centre has exponent `n-3`. Prior kernel-certified planar
  `topTwo_tailCount_le_two_of_card_ge_four` then implies ALL remaining
  centres have exponent `<= n-4`. The exact global dyadic conclusion
  follows. The absence of the third-highest layer off `s,a`
  is an explicit additional premise; it is NOT proved universally.

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39027270730:
**SUCCESS** at commit `d5226310a657e8b201eb74ce8696c07cd67d8069`,
3501 Lake jobs, `#print axioms` for both exactly
`[propext, Classical.choice, Quot.sound]`.

## 2. Main admitted lower-branch statement narrowed again

`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
now dispatches original <=2, 3, and 4 centre closures;
the previously added five-centre top/no-next case; and the new
five-centre top/next/no-third case above. Only the complement
continues into the same actual-edge six-source payment condition,
with ONE executable `sorry`.

The number of admitted obligations is still ONE: the quantified
geometric domain of its unique remaining branch is narrower.
Do not call this an unconditional global theorem while `sorryAx`
still occurs in its axioms.

Integration committed at `c759b53c3e78979af6da5b63a5aa7bb3c0a6286b`,
and targeted workflow verification was started at
https://github.com/Charlie-Wang-03/awards/actions/runs/39027392555 .
Integration CI should be checked independently; a successful local
math module alone does not verify the WIP source.

## 3. Historical Lean repair: interior saturation rigidity

`JSP000404Research/LinearBandInteriorSaturation.lean`:

- Corrected `Finset.card_insert_of_notMem` lemma name and membership
  equality orientation.
- Normalized `successiveDiffsFrom` and mapped `listExponent`.
- Supplied the sorted last-band lower bound
  `floor b <= floor (bs.getLastD b)` so arithmetic equality
  extraction from saturation becomes valid.
- Avoided aggressive unfolding of `List.getLastD` in the equal-band
  case by simplifying only the exact zero `excess`.

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39027359053:
**SUCCESS** at commit `751cc54900d07b30b36afe961f45af7d7e766d7f`,
3268 Lake jobs, both printed rigidity theorems with only
`[propext, Classical.choice, Quot.sound]`.
The earlier six reported diagnostics for this file are now zero.

## 4. Global open condition and build health

The actual retained-edge external TRUE-hole six-source payment must
still be proved. Specifically translated covered blockers, certified
duplicate debt, movable hard words, terminal twin/mixed rigid carriers,
soft overlap, and profile loss must be covered WITHOUT reuse by true
external holes plus actually unreserved dyadic surplus. Conditional
equivalences are not the requested existence proof.

The earlier Fast Incremental Lean run #39025320329 on prior SHA
`f8a6560d79139f8f67491856b76b3c54be4ccf2e` had 264
error diagnostics across historical modules; this is distinct from
the now successful targeted Lean checks. Full tree not claimed green.
Before reporting new full-tree error totals, inspect the latest completed
run's actual logs.

No arbitrary `AngleCap` counterexample has been established.
No new `sorry`, `admit`, or nonstandard axioms were introduced.
