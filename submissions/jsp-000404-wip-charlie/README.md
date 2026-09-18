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
  third top-level centre under the global cap `pi - lam`.

No theorem in this branch claims the missing general weighted Kraft bound.

## Deliberately open bridge

The remaining mathematical work is **not** hidden behind an axiom or `sorry`.
In particular, this branch does not yet formalize or assume:

1. the bridge from Sendov's local gap/exponent data
   `ell_i = n - k_i = a_i + p_i` to the predicate `SharpAt` when
   `ell_i = 1`;
2. the general Geometric Kraft inequality
   `sum_i 2^(-ell_i) <= 1` for `delta < 1/2`;
3. the upper-half inequality `sum_i 2^(-ell_i) <= 5/4`;
4. the thresholded compensated-deletion / zero-carry packing theorem.

These are the active proof gaps and must remain explicit.

## Reproduction

Pinned toolchain:

- Lean `v4.34.0`
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435`

From this directory:

```sh
lake exe cache get
lake build
```

The current ChatGPT execution environment does not have Lean installed, so this
commit has not been locally kernel-checked here.  Do not treat that as a CI pass.
