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

## Current hard stops and sharpened outlets

The following tempting strengthenings have now been adversarially tested and
must **not** be used as hidden assumptions:

- a fixed standard-band phase need not satisfy every local deficit budget;
- residual edges cannot in general always be absorbed into one of their two
  neighbouring retained colours;
- per-centre phase averaging need not satisfy
  `E_phase 2^(floorExcess b) >= 2^(floorExcess q)`;
- the coarse support inequality `sum_i 2^(-positiveSupport q_i) <= 1` is false;
- an arbitrary deleted centre need not create an exponent gain anywhere;
- the gain digraph need not contain the simple gain-closed core previously
  hoped for;
- the strong deletion-average condition `sum bonus >= W` is false;
- the exact-normalized global critical-turn conjecture
  `sum criticalWidth <= 2*(n+delta)` is false: two concentric regular
  heptagons (outer radius 1, inner radius 0.85, relative rotation pi/7) give
  `t ~= 13.4330`, `delta ~= 0.4330`, but total normalized critical width
  about `31.3191 > 2*t ~= 26.8661`;
- the weaker total critical bad-mass bound `sum badWidth < t` is also false:
  aligned concentric regular 13-gons near radius ratio 0.708 give
  `t ~= 26.4987`, `delta ~= 0.49868`, and summed bad-interval lengths
  about `37.83 > t`; the obstruction intervals overlap heavily;
- even the strengthening `measure(union bad intervals) <= t/2` is false:
  an aligned double regular pentagon near radius ratio 0.4525 gives union
  coverage about `0.6123*t`;
- "full vertex => every radial gap <= 1" is false.  The correct generic
  conclusion is that a full interlacing puts at most one partition boundary
  in each radial gap, while all partition-boundary spacings are <= 1; hence
  each radial gap is strictly shorter than two units and every quotient is
  <= 1.  Thus the Sendov floor-excess exponent is zero.

Closed replacements now available in Lean include:

- exact one-exception boundary domination and exact budget-failure structure;
- a bad local phase loses exactly one floor-excess unit at the exceptional gap;
- at such a bad phase the exceptional quotient is at least two, and the number
  of boundary-hit zero quotient gaps is exactly `(n - sum q) + 1`;
- zero-gain merges are completely characterized:
  no-carry requires at least one zero quotient, while one-carry zero gain
  requires both quotients zero;
- the sharp total-bonus deletion threshold:
  if `W < |V| + sum_r bonus r`, then some deletion is compensated.

The live global routes are therefore:

1. **fixed-phase wrap route:** prove directly that the union of wrap-triangle
   bad-phase intervals does not cover the phase circle.  Total-turn, total
   bad-mass, and half-circle-union bounds are no longer admissible shortcuts;
   any proof must exploit the strong overlap structure of the bad intervals;
2. **full-band / Hansel route:** find a phase with at most one fully specified
   standard-band vertex, or derive an equivalent defect statement.  A full
   generic vertex has zero Sendov floor-excess, but no global phase-existence
   theorem is proved yet;
3. **adaptive even-partition route:** generalize the Erdős--Szekeres narrow
   direction-interval reassignment while preserving bipartiteness/evenness;
4. **compensated-deletion route:** prove a restricted or dichotomic deletion
   theorem from the coupled radial orders of an actual planar configuration.


Numerical falsification is used only to kill over-strong conjectures; passing
random tests is never treated as proof.

### Notation / indexing warning

There are two different integer scales in the full Blumenthal/Sendov story and
they must not be conflated.

Inside Sendov Lemma 4.12,

[
t=u/2=n+delta,qquad n=lfloor tfloor,qquad 0ledelta<1,
]

and the lower-branch generalized-configuration target is

[
|P|=sum_i 2^{k_i}le 2^nqquad(delta<1/2).
]

This `n` is the integer part of the normalized angular parameter `t`.
It is **not** the outer dyadic index `m` used when the final Blumenthal
classification is written in ranges such as `2^m < N <= 2^(m+1)`.

For example, the final critical value just above `2^m` has
`GA = pi * (1 - 1/(2m+1))`, hence `t=2m+1`; therefore the Lemma-4.12
integer is `n=2m+1`, not `m`.

Consequences for this research branch:

- every theorem stated purely as an `n`-bit / `2^n` capacity theorem remains
  mathematically meaningful;
- `CriticalFiberBalance` is an internal critical-capacity counting lemma and
  must not be described as the original Blumenthal `N=2^n+1` case without an
  additional bridge;
- all future prose must distinguish the Lemma-4.12 integer `n=floor(t)` from
  the outer final-classification dyadic index.

### Exact-normalization correction

A later audit identified an important distinction in the numerical
falsification work.

Sendov Lemma 4.12 chooses the parameter u, hence t = u/2 = n+delta, from the
**actual equality**

  GA(V) = (1 - 2/u) * pi.

Several earlier adversarial searches instead fixed a looser external angle cap
and only required the sampled centre set to satisfy that cap.  Such slack-cap
counterexamples are valid against statements claimed uniformly for every
configuration below a fixed cap, but they do **not by themselves** refute a
statement restricted to Sendov's exact normalization.

Accordingly:

- exact algebraic counterexamples and exact-normalized geometric
  counterexamples remain hard stops;
- slack-cap numerical counterexamples are retained only as warnings against
  over-strong cap-uniform lemmas;
- new induction work should preserve an actual maximum-angle witness whenever
  possible.  If at most three top-level rank-one circles contain a maximizing
  angle triple, deleting a different top-level centre preserves the exact
  angle parameter.

This distinction is now part of the frozen research protocol.

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
