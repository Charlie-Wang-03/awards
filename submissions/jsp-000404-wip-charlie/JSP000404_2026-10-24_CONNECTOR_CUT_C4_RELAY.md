# JSP-000404 — connector cut/C4 formalization relay (2026-10-24)

## Source and scope

- Research-only branch: `research/jsp-000404-connector-compiler-repair-20261024`.
- Source parent: `aed4dc326a320b43890d73f9705edd62ea2d0106` on `research/jsp-000404-sharp-centre`.
- The original JSP-000404 theorem is **not proved or disproved**.
- The single intentionally admitted global obligation remains `planar_lower_branch_dyadic_capacity_admitted_wip` in `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`. Its `sorry` must not be hidden by changing the theorem statement or adding axioms.

## Compilation-repair chain

Two exact historical failing modules were selected from the downstream cut/C4 workflow [40101434355](https://github.com/Charlie-Wang-03/awards/actions/runs/40101434355).

1. `CutSpanNMinusOneQuotientShape.lean`: convert active-cardinality saturated truncation into additive equality via `omega`, correct arguments to the saturated seam and local-band API, and derive the normalized terminal floor bound directly from genuine real-valued bounds.
2. `CutMonochromaticC4Angles.lean`: resolve the implicit wrap phase `delta`, instantiate the boundary-bit separation with explicit vertices, pass implicit angle-vertex parameters by name, and transport merged colours through the proved `localIncidentColor_mergeLastPartition` identity.

Intermediate workflow [40102725873](https://github.com/Charlie-Wang-03/awards/actions/runs/40102725873) reduced the source error set to three elaboration errors; [40103211284](https://github.com/Charlie-Wang-03/awards/actions/runs/40103211284) diagnosed further downstream API/floor/rewrite errors. Latest changes are subject to the focused check [40103871287](https://github.com/Charlie-Wang-03/awards/actions/runs/40103871287). **A commit or CI run in progress is not a PASS.**

## Five-minimum genuine C4 colour obstruction

The research-only `FiveMinimaC4UniqueCanary.lean` aims to establish:

- Any two *simple* 4-cycles on five vertices share an unordered edge.
- Hence two edge-disjoint local-colour graphs on five minima cannot both carry 4-cycles.
- Consequently the number of genuine monochromatic C4 exceptional colours on five minima is at most one (strengthening the existing at-most-two bound).

A purely combinatorial reason: the four-vertex supports of two cycles intersect in at least three vertices. On any shared triple, each cycle contains at least two of the three possible internal edges. Two two-element subsets of a three-element edge set intersect.

This is a finite graph lemma, *not* a geometric six-source payment. Its initial brute finite Lean proof hit a GitHub runner shutdown (exit 143), not a verified type failure or proof success. The finite case proof was changed to simplify degenerate first-cycle tuples before kernel decision; latest [focused verification](https://github.com/Charlie-Wang-03/awards/actions/runs/40103687396) remains an external proof gate.

## True missing global proof

The live `AngleCap` argument needs a non-reusing charge of real translated-loss and terminal twin/mixed/soft/covered-blocker debts into TRUE uncovered Boolean words outside all translated slices and *genuinely unreserved* dyadic slack. Existing local cycle/triangle/C4 and exact matching lemmas have not established that global allocation. In particular, a finite graph colouring lemma does not provide any new true-hole credit.

No custom axiom, new admitted proposition, first-complete-priority assertion, or upstream submission is intended by this branch.


## Continuation: verified mathematical reductions, 2026-10-24

GitHub branch is `research/jsp-000404-connector-compiler-repair-20261024`; draft PR is https://github.com/Charlie-Wang-03/awards/pull/6.

### Kernel-certified results (full SUCCESS, no `sorryAx` in named theorems)

| Workflow | Target | Status |
| --- | --- | --- |
| [40103687396](https://github.com/Charlie-Wang-03/awards/actions/runs/40103687396) | `FiveMinimaC4UniqueCanary` | SUCCESS: five minima, at most one C4-bearing edge-disjoint colour |
| [40107208313](https://github.com/Charlie-Wang-03/awards/actions/runs/40107208313) | `CutBadFourConsecutiveStepShape` | SUCCESS, 9,115 Lake jobs: each positive ordinary step quotient equals one under the span-three assumptions |
| [40107649425](https://github.com/Charlie-Wang-03/awards/actions/runs/40107649425) | `SixPointBadActiveC4`, `SixPointBadSharedC4Colour` | SUCCESS, 3,252 Lake jobs: both bad minima must activate the SAME C4-bearing colour under exact 3,3,2,2,2 reduced profile |
| [40107649419](https://github.com/Charlie-Wang-03/awards/actions/runs/40107649419) | `CutSpanNMinusOneQuotientShape`, `CutMonochromaticC4Angles`, `TwoBadMonochromaticC4Incidence` | SUCCESS, 9,135 Lake jobs: one of two bad minima on a forced cycle has an AngleCap-based strict sub-lambda angle |
| [40108090562](https://github.com/Charlie-Wang-03/awards/actions/runs/40108090562) | `SixPointBadSharedC4FromEquality` | SUCCESS, 3,253 Lake jobs: original six-point exact-equality assumptions imply a single C4 colour active at both bad minima |

In the absence of independent geometric constraints, the stronger claim
that BOTH bad minima lie ON the same four-cycle is false.
The explicit 3-colour K5 witness and its on-cycle/off-cycle active profile
are in `JSP000404_2026-10-24_ABSTRACT_C4_PROFILE_SATISFIABILITY.md`.

### Latest conditional conjunction

`SixPointCutSharedC4SmallAngle.lean` connects the exact six-point shared
colour and the genuine uncovered-cut two-bad small-angle theorems under
their common AngleCap assumptions. Its focused gate is
https://github.com/Charlie-Wang-03/awards/actions/runs/40108455064 .
Treat the result as **pending** until the gate returns success and
`#print axioms` excludes `sorryAx`.

### Unsolved original theorem

The admitted theorem
`ProjectionOrdered.planar_lower_branch_dyadic_capacity_admitted_wip`
still has exactly one intended executable `sorry`. The remaining
global proof obligation is the nonreused allocation of translated-loss
blockers, duplicate canonical images, terminal twin/mixed/soft and
other losses against **true external Boolean holes** and **unreserved**
dyadic surplus under actual AngleCap geometry. Conditional accounting
identities are not a payment proof, and covered words are not hole
credits. Do not assert JSP-000404 solved on the basis of this research PR.


## Second continuation: pendant vertex and two independent small-angle approaches

### Verified new kernel result

- [Five-minima pendant gate 40110980528](https://github.com/Charlie-Wang-03/awards/actions/runs/40110980528): **SUCCESS**, 3,251 Lake jobs; `degree_eq_one_of_active_off_fourCycle_no_cycle_through` has only `[propext, Classical.choice, Quot.sound]`. This fixes the formerly missing bipartite 2-colouring/no-triangle proof, explicit 12-term 4-cycle witness, and Mathlib finite-neighbour API. The theorem concludes: if an active fifth vertex lies on NO four-cycle in a bipartite five-vertex graph containing a C4, its degree is exactly one.

### Two subsequent routes — do not presume CI success

1. `FiveMinimaPendantRepeatedSmallAngle.lean` and `TwoBadEachSmallAngle.lean` form a *pendant-aware* proof that EACH bad minimum has an actual non-top small angle. The exact bottleneck was the pendant lemma, now certified. [CI 40110980490](https://github.com/Charlie-Wang-03/awards/actions/runs/40110980490), checked separately; investigate all remaining elaboration errors before claiming both-angle result.
2. `CutMergedTwoBadSmallAngles.lean` has a shorter *direct original-exponent* proof via four minimum-minimum incident edges and three non-root merged colours, followed by boundary merge injectivity and genuine same-cut-band small-angle geometry. Compiler error from reintroducing `lam` after `AngleCap p lam` was fixed in `71c8c76f`; [CI 40111014343](https://github.com/Charlie-Wang-03/awards/actions/runs/40111014343).
3. The new `SixPointCutBothBadSmallAnglesDirect.lean` bypasses the original-exponent and C4 pendant proof packages for a stronger exact-active-bounds-only result: root-factorize the cut partition, use the certified `four_nonTop_edges_three_nonroot_colours_repeat` at EACH bad vertex, then apply the certified `actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad`. [CI 40110888692](https://github.com/Charlie-Wang-03/awards/actions/runs/40110888692). It is submitted, **not yet certified** at this checkpoint.

### Global proof boundary

The full theorem still needs ONE global six-source payment with a nonreusing injection into **actual true outside-translated Boolean holes** plus genuinely unreserved dyadic surplus. Small-angle witnesses are local geometry and alone provide neither that injection nor adequate surplus. New local modules must not be imported as a fake global proof.


## PROVEN shorter route: EACH bad minimum gets an actual small angle

**SUCCESS:** [40110888692](https://github.com/Charlie-Wang-03/awards/actions/runs/40110888692), 9,121 Lake jobs. The new stronger local theorem
`six_point_cut_both_bad_minima_have_strict_small_angles_direct` printed **only**
`[propext, Classical.choice, Quot.sound]`, not `sorryAx`.

Its exact input is the SAME six-point un-covered cut-merged active-card
bounds (`top ≤1, bad₁ ≤4, bad₂ ≤4, all other minima ≤3`),
both `CutSaturationBadAt`, and genuine `AngleCap` geometry.
Its conclusion provides a strict sub-`lam` non-top two-ray angle
**separately at EACH of the two bad minima**.

The proof is significantly shorter than the pendant-C4 alternative:
`six_point_two_exception_root_factorization`
→ `four_nonTop_edges_three_nonroot_colours_repeat` *twice*
→ `actual_angle_lt_lam_of_equal_uncovered_merged_color_at_saturation_bad` *twice*.
This requires NO monochromatic C4 and NO assumption that both bad minima
lie on a selected C4. The independent C4 uniqueness and pendant results
remain useful for different structural cases but are now *unnecessary*
for the two-angle consequence.

**Also SUCCESS:** [40111014343](https://github.com/Charlie-Wang-03/awards/actions/runs/40111014343), 9,116 Lake jobs: the existing
`uncovered_cut_two_bad_minima_have_small_nonTop_angles` original-exponent
terminal theorem, after correcting duplicated `lam` in its binder
sequence. Its axiom list is `[propext, Classical.choice, Quot.sound]`.

A stronger conjunction
`six_point_cut_shared_C4_and_both_bad_small_angles` is submitted in
`SixPointCutSharedC4BothBadAngles.lean`; follow its separate
[40111507155](https://github.com/Charlie-Wang-03/awards/actions/runs/40111507155)
kernel gate before making acceptance claims. The optional
pendant-aware proof file `TwoBadEachSmallAngle.lean` has a separate
[40111643182](https://github.com/Charlie-Wang-03/awards/actions/runs/40111643182)
gate. Those paths are NOT required by the verified direct two-angle theorem.

**Unsolved:** the all-cardinality original theorem still retains ONE genuine
`sorry` for the global nonreusing six-source payment into REAL external
Boolean holes plus genuinely unreserved dyadic surplus. A small angle at
two centres cannot be treated as a newly discovered hole or as spare mass.
