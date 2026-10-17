# JSP-000404 — sharp top-two tail and uniform support repairs (2026-10-17)

Repository: Charlie-Wang-03/awards
Research branch: research/jsp-000404-sharp-centre

## Current original theorem status

JSP-000404 has **not** been proved or disproved in full.
The genuinely global planar lower-branch net six-source payment
inequality remains unproved, with a single admitted executable
`sorry` in `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
(current line 647 at the starting HEAD of this pass).
All new successful focus builds are *local* independent formal
certificates, not a claim that the broad research root builds cleanly.

## Actual CI repair census

At the start of this continuation, branch HEAD was
`88f591ed09e834e1a36e6a36f1fe26904e831536`.
GitHub Actions `39010490227` (fast incremental) ended in failure.
Inspection of the actual Lean log found 261 error diagnostics
across 23 historical modules. These include issues unrelated to
the research modules touched here. That broad failure is not fixed
by the success of focused workflows below.

## Verified: second layer uniform support

`JSP000404Research/SecondLayerUniformSupportTwo.lean`:
repaired the shadowed `lam` implicit binder on
`four_secondLayer_has_two_supportTwo_uniform`.

Focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39012279535
**SUCCESS**.

This restores the original actual four-centre second-layer
support-two reduction and retains its explicit transition-quotient
arithmetic companion. No `sorryAx` is introduced by the repair.

## Verified: top centre uniqueness and old two-layer tail

`JSP000404Research/TopTwoTailMultiplicity.lean`:
- fixed incorrect `rcases` on an implication `x ≠ a → x = b`;
- fixed implicit `lam` shadowing in two geometric theorems;
- used explicit `Ne.symm` rather than equation field projection;
- imported `TailMajorizationCapacity` for the real `tailCount`
  definition.

First focused attempt 39012283251 failed in Lean and was repaired.
A subsequent check failed during Mathlib cache download because
the GitHub runner could not resolve `release.lean-lang.org`,
not because the theorem failed. The failed jobs were explicitly
rerun using the GitHub connector.

Final focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39012531099
**SUCCESS**, 3,498 Lake tasks.

`topExponent_eq_fixed_top` and `topTwo_tailCount_le_three`
have kernel axiom lists exactly
`[propext, Classical.choice, Quot.sound]`.

## Newly proved stronger real geometric tail bound

`JSP000404Research/SharpTopTailTwoMultiplicity.lean`:

`topTwo_tailCount_le_two_of_card_ge_four` states, for any
injective finite planar `AngleCap` configuration with at least
four actual centres, `n >= 3`, `0 <= delta < 1/2`,
`t = n+delta`, `lam = pi/t`, and a real centre `s` with
`centreExponent(C s) t = n-1`:

```
tailCount (fun i => centreExponent (C i) t) (n - 3) <= 2
```

The old theorem bounded that tail by 3.
The proof uses original actual planar top-centre uniqueness
and the kernel-verified global next-layer multiplicity
`actual_next_exponent_card_le_one_of_top`.
This is not merely a chosen-four-centre statement; it bounds
the global finite dyadic upper tail under these assumptions.

Focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39012531089
**SUCCESS**, 3,500 Lake tasks.

`#print axioms topTwo_tailCount_le_two_of_card_ge_four`:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

## Remaining mathematical frontier

These real geometric top-profile exclusions reduce the possible
high dyadic mass, but do not automatically pay covered loss and
NET duplicated source debts, and do not produce eligible true
Boolean holes or genuinely unreserved residual dyadic surplus.

Unresolved:
- unrestricted no-top support-two geometry and lower-layer profiles;
- six-source globally non-reused Boolean/dyadic allocation;
- cross-coordinate duplicate and target soft blocker ownership;
- historical broad Lean compile errors in unrelated files.

No research WIP merge to upstream or claim of reward eligibility
is justified at this point.
