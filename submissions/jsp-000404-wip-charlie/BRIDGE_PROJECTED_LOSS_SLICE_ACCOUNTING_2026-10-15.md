# JSP-000404 — Projected-loss coordinate accounting (2026-10-15)

Branch: `research/jsp-000404-sharp-centre`. Research-only: the full
JSP-000404 theorem is neither proved nor disproved.

## Verified exact accounting

The module `JSP000404Research/ResidualLossCoordinateSlices.lean`
already kernel-checks same-coordinate pairwise disjointness of the
translated projected-loss completion blocks.

With a choice of retained coordinate `choice(v) : Fin n` for each vertex,
write `T_c` for the **union** of the translated completion blocks of
the projected-loss vertices whose chosen coordinate is `c`.
For any exponent profile subject to the module's existing hypotheses:

```text
    2 * sum_c |T_c| = sum_{v in projectedLossVertices} 2^(exponent v).
```

This is a sum of the **individual slice cardinalities**. It is NOT
the cardinality of the union over distinct coordinates; cross-coordinate
overlap cannot be silently discarded. The unconditional identity
`two_mul_total_translatedLossSliceWords_card` was checked by focused
GitHub Actions run 38689006700 (success), at commit
`6aae7d197a4515c9668460703dcae370a3725e13`.

## Cross-coordinate conflict gate

The subsequent aggregate-level lemma
`translatedLossSliceWords_cross_collision_edge_colour` states
that whenever one actual Boolean word belongs to both `T_c` and
`T_d` for `c != d`, there are **distinct** projected-loss vertices
`v,w` owning the respective slices, joined by a **retained** edge.
Its retained edge colour equals either `c` or `d`.

The theorem is a lifting of the earlier proven source-level
`translated_loss_conflict_edge_colour` and does not assert that
cross-coordinate overlaps are absent. New source commit:
`468dda965b50068889ceb4796643bcfcb839b8e6`.
Its dedicated focused GitHub Actions run 38689297861 completed
successfully. This is a kernel-checked aggregate cross-coordinate
collision necessity theorem; it is not a no-collision assertion.

## Remaining proof obligation

A globally non-reusing accounting theorem must charge any
cross-coordinate loss overlap together with the existing NET duplicate,
soft-overlap, forward/reverse movable, equal-exponent twin and mixed-rigid
debts, using only literal **TRUE Boolean holes** and **independently
unreserved** dyadic surplus. Candidate slots, already-covered words,
and previously reserved credits are not interchangeable with those
resources.

The sole explicit `sorry` in
`PlanarLowerBranchProofAdmittedWIP.lean` is unchanged; it still
represents the actual global payment frontier. Neither the exact
slice sum nor the retained-edge classification closes this obligation.
