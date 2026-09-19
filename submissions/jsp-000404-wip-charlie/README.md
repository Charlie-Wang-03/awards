# JSP-000404 research WIP — Charlie downstream

This directory is a research-only Lean workspace for the still-incomplete
JSP-000404 / Erdős 504 / Sendov minimax-angle proof.

## Scope frozen in this branch

The Lean library currently contains only **closed consequences** that have
already been justified mathematically:

- the small-`delta` arithmetic inequality `2 * delta * lam < lam`;
- the Sendov-normalized inequality `3 * delta * lam < pi`;
- impossibility of three pairwise-distinct sharp centres once every angle at
  each sharp centre is bounded by `delta * lam`;
- in the first branch `delta < 1/2`, two sharp centres leave no room for a
  third top-level centre under the global cap `pi - lam`;
- the weighted Hansel / Erdős--Szekeres partial-code inequality and the exact
  defect form `sum_v (2^(free v) - 1) <= 2^k - |V|`;
- one-missing and all-missing consequences of the weighted defect bound;
- the exact zero-carry identity `ell = (n - Q) + p`;
- unit-deficit rigidity: `ell = 1` forces exactly one positive quotient gap
  and `sum q = n`;
- the fractional remainder budget and exceptional-gap arc budget;
- linearization of a unit-deficit cyclic gap system after cutting at its unique
  exceptional gap;
- the signed projective-interval geometry that turns one short ray interval
  into `ProjectiveCloseAt` and then `SharpAt`;
- `KraftCertificate`, `OrderedEdgeColoring`, and `BinaryEdgePartition`
  interfaces reducing the global sharp bound to explicit partial-code /
  active-colour constructions;
- ordered-direction base capacities `3 -> 3/2`, `4 -> 2`, `5 -> 5/2`,
  and `6 -> 3`;
- binary carry and local gap-merge arithmetic;
- whole-centre exponent monotonicity and +1/+2 merge-gain criteria;
- abstract compensated deletion, including a single-gain payment rule;
- the gain-closed-core minimum-exponent reduction.

No theorem in this branch claims the missing arbitrary-cardinality sharp
capacity bound.

## Deliberately open bridges

The remaining mathematical work is **not** hidden behind an axiom or `sorry`.
In particular, this branch does not yet formalize or assume:

1. the final cyclic-order / ray-representation bridge completing
   `ell_i = 1 -> SharpAt`; all arithmetic and signed-ray geometry around that
   bridge are already isolated in separate modules;
2. the general lower-half capacity theorem;
3. the general upper-half capacity theorem;
4. an existence theorem producing either
   - a compensated deletion, or
   - an adaptive even edge partition with sufficiently many locally missing
     colours,
   from the global ordered-direction / centre-gap geometry.

## Current research invariant

The published Sendov Lemma 4.12 correctly reduces a perfect generalized
configuration to

`|P| = sum_i 2^(k_i)`

with each `k_i` computed from the cyclic angular gaps at the rank-one centre.
The unresolved step is the claimed global maximization of this weight profile.

The downstream replacement route is deliberately weaker:

1. deleting a centre merges exactly two adjacent gaps at every survivor;
2. the survivor exponent never decreases;
3. two positive adjacent quotients, or a suitable binary carry, force at least
   one exponent unit of gain;
4. if the induced post-deletion weight gain pays the deleted centre, ordinary
   induction on the number of top-level centres closes;
5. alternatively, an adaptive even partition with local active-colour count
   at most `ell_i = n-k_i` closes immediately through weighted Hansel.

This route does **not** require classifying a unique extremal exponent profile.

## Source audit

The relevant primary-source gap is explicit in Sendov's 1995 proof of Lemma
4.12: after concrete calculations for `s = 2,3,4`, the text assumes the
lemma for `s-1` and then states the general maximizing exponent profiles for
`s` without deriving them from the induction hypothesis.  This is the step
that must not be imported as a proved lemma.

Erdős--Szekeres (1960) supplies the independent graph-theoretic engine used
here: even partitions, the `2^n` capacity bound, and the weighted
missing-colour defect.  Their Theorem 2 also demonstrates that narrow direction
intervals may be reassigned between colours while preserving evenness, which
motivates the adaptive-edge-partition branch of the current proof search.

Public partial formalizations were also checked:

- PR #100: exact N=5--10 and dyadic thresholds;
- PR #300: scoped small/dyadic formalization;
- PR #647: eleven-point direction bound and exact N=11--15.

These packages all leave the arbitrary-N classification open.  In particular,
the N=9 and N=11 machine certificates use the same abstract direction model
(range + two-branch triangle constraints) as the current ordered-direction
reduction; they do not reveal an additional geometric hypothesis that would
trivialize the general bridge.

## Reproduction

Pinned toolchain:

- Lean `v4.34.0`
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435`

From this directory:

```sh
lake exe cache get
lake build
```

The current ChatGPT execution environment does not have Lean installed, so the
new commits have not been locally kernel-checked here. Do not treat them as a CI
pass until an actual Lean build succeeds.
