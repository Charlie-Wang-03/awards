# JSP-000404 — Third-layer top-exponent and fifth-exposure exclusion

**Date:** 2026-10-16  
**Branch:** `research/jsp-000404-sharp-centre`  
**Overall problem status:** OPEN — no unconditional JSP-000404 proof/disproof.

## Certified top exponent rigidity

File `JSP000404Research/TopExponentSupportOneTransition.lean`.

- `top_exponent_positiveSupport_eq_one`
- `top_exponent_transition_qe_eq_n`

CI [38850183517](https://github.com/Charlie-Wang-03/awards/actions/runs/38850183517) **SUCCESS**, 3,443 build jobs.
Both `#print axioms` outputs are only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

For a concrete centre C at scale t=n+delta, with n>=2,
0<=delta<1, sum of canonical quotients <=n, and
`centreExponent C t=n-1`, the exact identity
`sum(q)=floorExcess(q)+positiveSupport(q)` forces its
positive support to equal one. The sole nonzero quotient is
then exactly n, hence every concrete high-exponent transition
certificate H satisfies H.qe=n. This replaces an undeclared
`unit_deficit_transition_qe_eq_n` reference.

## Certified five-support-arc packing contradiction

File `JSP000404Research/ThirdLayerNoFifthExposed.lean`.

`no_fifth_strictlyExposed_of_top_supportOne_two_supportTwo_deficitThree`

CI [38850503335](https://github.com/Charlie-Wang-03/awards/actions/runs/38850503335) **SUCCESS**, 3,457 build jobs.
`#print axioms` uses only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Hypotheses: `n>=4`, `0<=delta<1/2`, `t=n+delta`,
`lam=pi/t`, `AngleCap p lam`, and five distinct centres
`s,a,b,c,d`. Four centres satisfy

- `centreExponent Cs t=n-1` at s;
- `centreExponent Ca t=n-3`, positive quotient support 1 at a;
- `centreExponent Cb t=centreExponent Cc t=n-3`,
  each with positive quotient support 2 at b,c.

The fifth centre d CANNOT be `StrictlyExposedAt p d`.
Indeed, strictly supporting dual arc lengths are bounded
below by `n*lam`, `(n-2)*lam`, `lam`, `lam`, `lam`.
Global interval packing bounds their sum by `2*pi`, but
`(2*n+1)*lam > 2*(n+delta)*lam=2*pi`.

The Lean proof repairs were:

- Align the `lam` binder before `AngleCap p lam`.
- Replace missing `unit_deficit_transition_qe_eq_n` by
  the verified top support-one theorem.
- Convert the five heterogeneous support certificates to a
  dependent `Fin 5` family via `rcases ...; interval_cases`
  following the existing certified four-centre pattern.
- Explicitly enumerate the five certificate lengths and
  use the positive gap `(1-2*delta)*lam>0` for contradiction.

## Distinct residual problems

This theorem only excludes an additional **strictly exposed** centre
from the specified third-layer 1+2+2 extremal pattern. It does
not forbid fifth NONEXPOSED centres, eliminate other support
distributions, or imply that the global six-source debt can be
paid by actual outside-U holes and genuinely unreserved surplus.

The main WIP theorem
`PlanarLowerBranchProofAdmittedWIP.lean` still contains one executable
`sorry`. New modules introduce no admission. A focused Lean success
does not establish a full-workspace green build.
