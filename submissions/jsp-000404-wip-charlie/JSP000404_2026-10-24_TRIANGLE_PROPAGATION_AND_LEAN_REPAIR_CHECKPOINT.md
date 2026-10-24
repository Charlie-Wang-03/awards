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
