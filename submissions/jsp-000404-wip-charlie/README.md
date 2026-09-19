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
- the weighted Hansel / Erdős--Szekeres partial-code inequality;
- its exact defect form
  `sum_v (2^(free v) - 1) <= 2^k - |V|`;
- the consequences `|V| + 1 <= 2^k` when one vertex has a missing Boolean
  coordinate, and `2 * |V| <= 2^k` when every vertex has one;
- the exact zero-carry identity `ell = (n - Q) + p` in abstract finite-sum form;
- the partial-cube `KraftCertificate` interface reducing the lower sharp
  capacity bound to a concrete Boolean-code construction;
- ordered-direction base capacities `3 -> 3/2`, `4 -> 2`, `5 -> 5/2`, and
  `6 -> 3`.

No theorem in this branch claims the missing general sharp capacity bound.

## Deliberately open bridge

The remaining mathematical work is **not** hidden behind an axiom or `sorry`.
In particular, this branch does not yet formalize or assume:

1. the bridge from Sendov's local gap/exponent data
   `ell_i = n - k_i = a_i + p_i` to the predicate `SharpAt` when
   `ell_i = 1`;
2. the sharp ordered-direction capacity theorem in the lower branch;
3. the upper-half sharp ordered-direction capacity theorem;
4. the thresholded compensated-deletion / endpoint-slack recurrence that
   should convert ordered-direction data into the weighted Hansel defect
   accounting.

The active research route is to prove the sharp capacity directly from the
ordered-direction constraints, using Erdős--Szekeres even-partition / missing-
colour defect accounting rather than the disputed general capacity-maximization
step in Sendov's published argument.

The finite five-/six-point orientation-elimination architecture was cross-checked
against the already-public scoped formalization in TheJustinSunPrize/awards PR
#300.  Those base-case techniques are treated here as prior public formalization,
not as a priority claim.  The new research target is the general capacity bridge.

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
