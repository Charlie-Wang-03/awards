# JSP-000404 — Geometric/Hall proof-chain and Lean repair checkpoint (2026-10-23)

Repository: `Charlie-Wang-03/awards`; research branch: `research/jsp-000404-sharp-centre`.

**Status: PARTIAL, NOT A PROOF OR DISPROOF OF JSP-000404.** No claim of an all-tree Lean build or upstream award acceptance is made.

## Independently verified mathematical lemmas

### Actual minimal-Hall collision accounting

`JSP000404Research/MinimalBlockSharedDeficit.lean` passed focused CI
[#39813293198](https://github.com/Charlie-Wang-03/awards/actions/runs/39813293198) (3094 Lake jobs).
In an inclusion-minimal deficient block family `T`, for each locally adequate
block `v`, with deficit `D(T)>0`, local slack
`s(v)=card(B(v))-demand(v)`, actual collision neighbours
`N_T(v)={z in T\\{v}: B(v) cap B(z) nonempty}`, and a uniform pairwise
intersection bound `card(B(v) cap B(z)) <= k`, Lean proves

```
D(T) + s(v) <= k * card(N_T(v)).
```

This counts pairwise collision incidences, **not** non-reusable Boolean words,
and alone does not solve the six-source payment.

### Two forced mixed support-three three-transition centres

`JSP000404Research/MixedSupportThreeNonExposed.lean` passed focused CI
[#39819858679](https://github.com/Charlie-Wang-03/awards/actions/runs/39819858679) (3463 Lake jobs).
The two exported theorems
`mixed_support_one_has_two_nonexposed_support_three` and
`mixed_support_one_has_two_three_transition_centres`
have only the standard axioms `propext`, `Classical.choice`, `Quot.sound`,
without `sorryAx`.

Under the six-original-centre profile with `n>=5`, one exponent `n-1` top,
five exponent `n-3` minima, and one support-one minimum `a`, the proof finds
two distinct further minima `b,c` that are neither `a` nor the top.
Both have `positiveSupport=3`, are **not** strictly exposed and have a
concrete lifted sign path with exactly three sign transitions.

The first theorem is now explicitly imported in `JSP000404Research.lean`.
This is an unconditional local geometric classification under the stated
six-centre profile, **not** an exclusion of that profile.

**Exact remaining geometry bridge:** `HighExponentTransitionPacking` charges
one `HighExponentTransitionIntervalCertificate` per centre.
`exists_highExponentTransitionIntervalCertificate` uses
`n-2 <= centreExponent`. The forced support-three minima instead have
`centreExponent=n-3`, so its current existence theorem does NOT apply.
A multi-transition packing/dedicated geometric exclusion or another genuine
deletion/payment bridge is still required. Do not silently insert these minima
into the `2*n` transition packing theorem.

### Unsafe saturated edge zero-wrap witness

`JSP000404Research/ResidualUnsafeSaturatedWrap.lean` passed focused CI
[#39820170436](https://github.com/Charlie-Wang-03/awards/actions/runs/39820170436) (3272 Lake jobs).
`unsafe_residual_saturated_pair_has_zero_wrap_endpoint` proves that an
unsafe residual pair with both endpoint cycles projected-saturated has at least
one endpoint with zero cyclic wrap excess. The module uses the actual
`LocalDirectionCycle.exists_saturated_zero_wrap_value_decomposition`.
The exported theorem is sorry-free.

## Source-level Lean repair attempts still requiring independent validation

At baseline commit `b2f600f61d8d2f6f7c1711685d5c2325870cfac4`,
the fast incremental CI
[#39814535514](https://github.com/Charlie-Wang-03/awards/actions/runs/39814535514)
failed with **118 compiler diagnostics over 13 files**.
This is a historical baseline, not a claim about the current head.

Repairs committed to the research branch:
- `SixPointExactWitnessTerminal`: explicit angle/type-variable binder order.
- `SixPointUnitPhaseCoverAllN`: explicit `lam` binder before `AngleCap`.
- `SixPointHardSupportReduction`: bind the non-top witness `hi_ne_top`
  before using it in a dependent result type.
- `CentreAdjacentTransitionOccurrence`: actual indexed quotient bounds,
  concrete mapped-sign decomposition, and predecessor list-length proof.
- `SixPointMixedSupportTransitionBudget`: use the previously verified
  `Fin` index-case convention and index-specific certificate equalities.
- `MixedSupportThreeNonExposed` and `ResidualUnsafeSaturatedWrap`:
  independently verified as described above.

The four-module focused legacy build
[#39819238271](https://github.com/Charlie-Wang-03/awards/actions/runs/39819238271)
and the mixed transition budget focused build
[#39821033351](https://github.com/Charlie-Wang-03/awards/actions/runs/39821033351)
must be consulted for their actual results; this note does not pre-approve them.

## Actual unresolved theorem and scientific restrictions

`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
retains one intentionally executable `sorry` in the global planar lower
branch theorem. Its `#print axioms` still includes `sorryAx`.
The real missing global inequality requires a disjoint/non-reusing allocation
of genuine Boolean holes, net movable hard sources, same-target duplicate
fibres, covered soft overlap, equal-exponent twin rigid carriers, both
mixed-rigid debts, projected loss and **unreserved** dyadic surplus.
A covered soft word or a repeated collision word is NOT a true hole.
A passing focused build is not equivalent to an all-research-tree build.
