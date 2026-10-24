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
