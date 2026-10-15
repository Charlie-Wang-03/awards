# JSP-000404 — Certified one-sided actual-edge loss blockers (2026-10-15)

## Scope

Research-only continuation on `research/jsp-000404-sharp-centre`. The
original JSP-000404 conjecture is neither proved nor disproved. The sole
executable `sorry` in
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` remains open.

## New kernel-certified structural results

Module:
`JSP000404Research/ResidualLossActualEdgeCarrierFrontier.lean`.

1. `chosenLossActualEdgeBlockerTriples_no_straddle`. For a fixed
   projected-loss source `v` and selected retained flip colour
   `choice v`, it is IMPOSSIBLE for both a left blocker `a < v`
   and a right blocker `v < b` to occur in the **actual-edge**
   chosen-blocker-triple family. Otherwise the ordered path `a < v < b`
   would have the same original edge colour on both edges, violating
   `OrderedEdgeColoring.noMonoTwoPath`.
2. `chosenLossActualEdgeBlockerTriples_one_side`. For every fixed source
   `v`, either ALL actual chosen-colour blockers lie strictly below
   `v`, or ALL of them lie strictly above `v`. The empty family
   satisfies both options.

This is an unconditional necessary geometry restriction for the existing
actual chosen-edge carrier family. It relies on the *true* ordered-colour
axiom, NOT on the stronger, false assumption that edge colours are proper
at every vertex. Several blockers on the SAME side are still possible.

**Verification:** commit
`becd85c19adf9c32e19f0f5358ec5a59d38594a7`, focused GitHub
Actions run **38738565326: SUCCESS**, 3316/3316 build jobs. Both new
theorems have the explicit kernel axiom set
`[propext, Classical.choice, Quot.sound]`; NO `sorryAx`.

## Independently verified Lean repair

- `MergedBandMap.lean`: explicit positive-width Fin-zero construction,
  normalization of `0 != n`, correct `Nat.floor_eq_zero` hypothesis,
  equality orientation, and `Finset.mem_erase` API.
- `SupportTwoThreeCycle.lean`: correct three-way disjunction case split
  and normalized opposite-order sums before the final `omega`.
- Dedicated workflow:
  `.github/workflows/jsp000404-focused-legacy-merge-cyclic.yml`.
- Repair commit
  `6073cb8cc7ae4e607f21321836440752ef637aa2`, focused
  GitHub Actions run **38738284639: SUCCESS**.

These focused successes do NOT establish a successful full-workspace
incremental build; many independent historical modules are still
outside the certified boundary.

## Exact remaining proof frontier

For a retained-active selected loss-flip assignment `choice`, the
verified exact six-source reduction requires

```text
terminalTwinOtherFiveDebt
  + |actual same-colour retained-edge blocker triple UNION|
  + translatedLossDuplicateDebt
<= |TRUE holes outside the translated loss union|
  + genuinely unreserved terminalTwinAvailableSurplus.
```

The new theorem shows that, for each loss source, the triple family
supporting the blocker union lies on only ONE order side. This is a
genuine reduction in admissible blocker configurations, but does NOT
yet bound the total Boolean union strongly enough to pay the full
six-source debt. It does not prove disjointness, eliminate repeated
same-side blockers, convert already-covered words into holes, or
produce a globally non-reusing allocation.

**Next mathematical target:** combine the proved one-sided blocker
structure with actual planar `AngleCap` incidence and retained-bit
geometry to derive a quantitative capacity/payment bound on the
real blocker union. The resulting credit must be combined with
cross-coordinate duplicate debt and the five other terminal debt
classes, without reusing any true hole or already reserved surplus.

No full original-problem theorem, upstream submission, or formalizer
priority claim follows from the present increment.
