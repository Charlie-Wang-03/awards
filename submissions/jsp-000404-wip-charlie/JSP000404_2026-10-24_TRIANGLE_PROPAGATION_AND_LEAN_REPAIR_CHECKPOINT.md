# JSP-000404 — triangle propagation and compiler repair (2026-10-24)

Research-only checkpoint on `research/jsp-000404-sharp-centre`; **NOT a proof or disproof** of JSP-000404 / Erdős 504.

## Newly kernel-certified original-plane geometry

Commit [a76f4199](https://github.com/Charlie-Wang-03/awards/commit/a76f419905a6695b6a47f6a3460781e92890cb75) adds `JSP000404Research/SeparatedSupportTwoTrianglePropagation.lean` and imports it through the research umbrella.

Verified by [focused CI run 40063627498](https://github.com/Charlie-Wang-03/awards/actions/runs/40063627498), **PASS**, 3553 Lake jobs, no Lean errors. Its `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`.

Proof principle: An original planar `AngleCap p lam` triangle with distinct vertices (s,a,b) and actual small angle
`angle(a,s,b) <= delta * lam` satisfies both opposite lower bounds
`angle(s,a,b), angle(s,b,a) >= (1-delta)*lam`, from the triangle angle sum and global angle cap. If `lam>0` and `delta < 1/2`, each opposite angle is *strictly larger* than `delta*lam`.

The certified six-centre specialization
`separated_support_two_has_non_top_triangle_two_large_angles` produces two distinct non-top ray endpoints (x,y) at a separated support-two minimum (i), with the actual central angle `<=delta*lam` and both actual opposite angles `>delta*lam`. This uses the previously kernel-certified `separated_support_two_has_small_pair_away_from_top` ([CI 40062487650](https://github.com/Charlie-Wang-03/awards/actions/runs/40062487650), PASS, 3552 Lake jobs).

**Scope warning:** A local small-angle triangle cannot be double charged at a second vertex, but the above does not provide any injective allocation into TRUE uncovered Boolean words or actually unreserved dyadic surplus. It does not close the six-source global payment.

## Compilation diagnostics and repairs

The historical full incremental [run 40060010554](https://github.com/Charlie-Wang-03/awards/actions/runs/40060010554) failed with 137 errors in eight modules. A subsequent cancelled run 40062487674 reached 101 errors in seven modules, a partial and **non-final** signal; a cancelled job is not a green or red acceptance verdict.

This turn made source repairs in commits:

- [a982ffa2](https://github.com/Charlie-Wang-03/awards/commit/a982ffa2246f1e0b67793a0b94c90dd3f945a405): FiveMinimaColourGraph finite neighbor witness and Boolean disjointness, SixPointHardLowSupportGeometry lambda binding and proof-parameter orientation, CutSaturatedSupportMismatch normalized band labels, CutMergedRepeatedSmallAngle explicit lambda/delta and boundary bit.
- [942b7efe](https://github.com/Charlie-Wang-03/awards/commit/942b7efed5c34e8528c13ef53121b012b38a4911): ResidualEnlargedCollisionSimpleGraph uses the established `exact_projected_loss_rigidity` instead of a nonexistent residual-inactive lemma and replaces two outdated finite-cardinality API calls.
- [29cf7415](https://github.com/Charlie-Wang-03/awards/commit/29cf74156f082510ad083222d72430dc70a88549): SixPointOrdinaryInsideBadPalette finite-filter induction and card-insert API.
- [a653b59d](https://github.com/Charlie-Wang-03/awards/commit/a653b59db8afb5a35558ab311531bfbf036571e0): six-point palette erased-vertex membership orientations and nonlinear commutative product arithmetic.
- [275238e0](https://github.com/Charlie-Wang-03/awards/commit/275238e0322508f743efbc11e10160918d7a263a): focused CI workflow for five previously failing hard-branch modules.

The repairs above are **not claimed kernel-passed** until their respective newest GitHub Actions run succeeds. The focused hard-branch run is [40064298582](https://github.com/Charlie-Wang-03/awards/actions/runs/40064298582) (pending/running at checkpoint creation); do not mistake older cancelled attempts for a verified failure. The umbrella build is not green based on focused runs alone.

## Single genuine sorry and exact research frontier

File: `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` at approximately line 900, inside `planar_lower_branch_dyadic_capacity_admitted_wip`.

The conditional `PlanarLowerBranchActualEdgeCarrierFrontier` remains sorry-free, but its needed global non-reusing payment is genuinely unproved. At the precise frontier, an active loss-coordinate choice must pay terminal twin/other-five debt, the ACTUAL same-colour covered retained-edge blocker union, and translated-loss duplicate debt against TRUE holes outside translated loss slices plus genuinely unreserved terminal surplus.

Proved separate simplifications already recorded elsewhere: n=1 and n=2 all-cardinality capacity; card<=4 small-centre cases; for <=7 centres NET duplicate debt is zero by the true hard-carrier eight-centre barrier; for <=9 centres genuine NET duplicate and twin-rigid debt cannot both be positive. None by itself pays covered blocker, soft, mixed, twin, or other debt. The locally certified small-angle triangles have not been shown to furnish a globally injective TRUE-hole payment.

**No `sorry` has been discharged at this checkpoint**, and no new axiom, `sorry`, external assumption or original-problem complete-proof claim has been introduced.


## 2026-10-24 later checkpoint — precise double-zero budget (kernel PASS)

The stronger real-plane theorem \`separated_support_two_double_zero_middle_angle_budget\` was implemented in \`SeparatedSupportTwoResidualBudget.lean\`. Verified by [focused CI run 40065565121](https://github.com/Charlie-Wang-03/awards/actions/runs/40065565121): **3553 Lake jobs PASS** and \`#print axioms\` lists \`[propext, Classical.choice, Quot.sound]\` only.

For an arbitrary finite set of centres (not just six), assume original planar \`AngleCap\`, an actual sharp-top exponent \`n-1\`, a distinct deficit-three centre exponent \`n-3\`, \`positiveSupport=2\`, \`n>=5\`, and \`0<=delta<1/2\`. An actual ray/quotient rotation pinning the top at the head exists. If BOTH first and final quotient gaps are zero, the **sum of all middle zero-gap ACTUAL angles** is bounded above by \`(3*delta-1)*lam\` and \`delta>=1/3\`. The proof deducts TWO distinct outer-angle lower bounds of \`(1-delta)*lam\` each from the exact \`(1+delta)*lam\` zero-angle mass bound; all geometry and lists are kernel checked. No global injection or true-hole credit follows automatically.

### Confirmed restoration of five difficult Lean modules

[Focused hard-branch CI 40065984799](https://github.com/Charlie-Wang-03/awards/actions/runs/40065984799): **PASS, 9148 Lake jobs, zero Lean errors**. In particular \`outside_bad_colour_used_by_exactly_two_ordinary\`, \`exists_ordinary_reduced_active_subset_bad\`, \`six_point_hard_lowSupport_geometry\`, and \`localColourGraph_neighborFinset\` have \`#print axioms\` free of \`sorryAx\`.

These proofs are genuine formalized necessary conditions for the two-bad-minimum six-point cut and the non-gaining low-support geometry; they do not prove the global payment.

### Remaining major engineering gate: enlarged collision graph

The previous incremental compilation logged 47 errors in \`ResidualEnlargedCollisionSimpleGraph.lean\` (older run 40065565159, ultimately CANCELLED after branch updates, **not** a valid final acceptance).

- \`4db3a636\`: relocates three genuine later-defined theorems above their early uses; adds a shared-word/source-block inclusion theorem using existing verified \`sharedBlockWords_has_other_block\`.
- \`3a246c3a\`: expresses tree leaves by unique adjacency rather than requiring an unsynthesizable \`Fintype\` instance for a parametrized neighbour set in the theorem statement.
- \`f1a335c4\` and \`6e44d4da\`: formally derive the exact projected-loss retained-active count with the correctly associated natural subtraction \`n + 1 - exponent(v)\`; the tempting \`n - exponent(v) + 1\` is **not valid without extra hypotheses** at the zero-cardinality boundary.
- \`b3a6a9fd\`: corrects malformed YAML in a new focused enlarged-collision workflow. The intended CI is \`JSP-000404 Focused Enlarged Collision Compilation\`. Latest available run after the active-count correction: [40066491073](https://github.com/Charlie-Wang-03/awards/actions/runs/40066491073), at this checkpoint **not yet validated**.

The root umbrella’s whole-tree compilation remains **UNVERIFIED** after these changes, and the sole intentional \`sorry\` remains in \`PlanarLowerBranchProofAdmittedWIP.lean\` at the genuine six-source external TRUE-hole/non-reused surplus allocation. These structural repairs are not a proof of global geometry.
