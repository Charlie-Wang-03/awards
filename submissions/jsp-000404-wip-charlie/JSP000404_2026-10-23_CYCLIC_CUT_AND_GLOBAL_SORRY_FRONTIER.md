# JSP-000404 — Cyclic Cut Geometry & Global Proof Frontier (2026-10-23)

## Scope / no overclaim
Work was committed to the **downstream** research branch
`research/jsp-000404-sharp-centre` of `Charlie-Wang-03/awards`.

**The original JSP-000404 is NOT proved or disproved.**
The original global proof
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
still has its **one genuine executable `sorry`** for global,
non-reusing, all-source dyadic/true-Boolean-hole payment.
No `axiom`, `admit` or axiom-equivalent hypothesis was inserted into
that root theorem. Separate focused proofs must not be represented as
a passing full-tree build.

## Previous focused CI independently confirmed
* Ordinary/Wrap cut adjacency to a canonical cyclic q=1 slot:
  [39926680717](https://github.com/Charlie-Wang-03/awards/actions/runs/39926680717), **PASS**.
* Non-vacuous finite-period actual critical-slot no-cover:
  [39926404073](https://github.com/Charlie-Wang-03/awards/actions/runs/39926404073), **PASS**.
* Original six-centre short triangle phase avoidance:
  [39926896097](https://github.com/Charlie-Wang-03/awards/actions/runs/39926896097), **PASS**.

## This continuation — kernel-verified focused modules
1. `CyclicCriticalUnitPhase.lean`:
   [39932242984](https://github.com/Charlie-Wang-03/awards/actions/runs/39932242984)
   **PASS**, 9,073 Lake jobs.
   `exists_uncovered_elevenPhase_of_six_point_terminal`
   and its circular separation prerequisites compile with
   `#print axioms` omitting `sorryAx`.
   An actual canonical q=1 unit-gap slot generates a periodic
   `delta`-arc; 11 circularly separated samples cannot fit into
   <=10 such slots for n>=5 and 0<=delta<1/2.
   The `s` in the over-approximating bad-phase predicate is allowed
   to range in [1,1+delta] rather than fixed to the original quotient
   gap's exact scaled length; this is a conservative enlargement.
2. `SixPointTrianglePhaseTerminal.lean`:
   [39932360969](https://github.com/Charlie-Wang-03/awards/actions/runs/39932360969)
   **PASS**, 9,095 Lake jobs.
   Invalid dependent triangle structure replaced by an abbreviation of
   the **same existential original-geometry short-triangle certificate**,
   retaining the three older theorem names. No `sorryAx`.
3. `CutCriticalToCyclicBadPhase.lean`:
   [39932884725](https://github.com/Charlie-Wang-03/awards/actions/runs/39932884725)
   **PASS**, 9,074 Lake jobs.
   `cut_adjacent_critical_bad_implies_cyclic_unit_bad`: exact
   original cut-adjacent scaled gap s in [1,1+delta] with BOTH critical
   bad-phase endpoint inequalities yields one canonical periodic global
   unit-gap bad slot at the SAME phase; ordinary and wrap cases are
   transported by the already checked cut adjacency bridge. No
   `sorryAx`.
4. `SixPointCyclicCutCriticalAvoidance.lean` initial theorem:
   [39932892399](https://github.com/Charlie-Wang-03/awards/actions/runs/39932892399)
   **PASS**, 9,075 Lake jobs.
   `six_point_exists_elevenPhase_without_cut_critical`: one of the
   eleven normalized period samples avoids **every** actual original
   centre / cut / adjacent critical interval certified in the precise
   `ExistsCutAdjacentCriticalBadAt` proposition, including cyclic
   wrap adjacency. No cover lower-bound or real-line infinite cover
   assumption, no `sorryAx`.

## Submitted, requiring final CI review
* `SixPointCyclicCutCriticalAvoidance.lean` further exposes
  `six_point_exists_period_phase_without_cut_critical` and
  `six_point_no_full_period_cut_critical_cover`, converting the
  eleven-sample theorem to `0 <= x < t` physically meaningful phase.
  Focused check:
  [39933542695](https://github.com/Charlie-Wang-03/awards/actions/runs/39933542695).
* `DeficitThreeSupportThreeRemainder.lean` attempts to repair the
  original exact-support-three pointwise fractional remainder proof
  using map-index alignment, verified list decomposition lemmas, and
  nondependent congruence rather than giant recursive simplification.
  Focused check:
  [39933367930](https://github.com/Charlie-Wang-03/awards/actions/runs/39933367930).
  Do NOT claim either as kernel-verified until check succeeds.

## Actual original remaining mathematical issue
The new n>=5 six-centre result rules out exhaustive coverage of all
phases by the precise cut-adjacent critical interval certificates.
However, **a failure of the original dyadic inequality has not been
proved to force the presence of these certificates for every phase**.
More broadly, the six-source global Boolean-hole payment needs a
single non-reusing allocation among literal unoccupied words, genuine
unreserved dyadic surplus and all hard/soft/twin/mixed-rigid/NET
duplicate/projected-loss debts. A covered word or candidate unit slot
is not automatically a TRUE Boolean hole or unreserved credit.
Neither the new cyclic phase theorem nor the old local slot accounting
supplies this global allocation.

The latest pre-continuation incremental whole-research-tree build
[39927532286](https://github.com/Charlie-Wang-03/awards/actions/runs/39927532286)
was a FAILURE (127 Lean errors in 11 module paths, notably
`ResidualEnlargedLossDegree` and several saturated-loss/dyadic files).
This is only a snapshot; rerun whole-tree after isolated repairs before
revising the overall status.

The status of the upstream prize should NOT be changed to solved.
