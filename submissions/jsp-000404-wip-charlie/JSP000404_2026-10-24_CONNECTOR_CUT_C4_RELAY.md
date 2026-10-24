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
