# JSP-000404 — refined no-top dyadic profile and geometric Lean repairs

Date: 2026-10-17. Branch `research/jsp-000404-sharp-centre`.
This report records kernel-checked **conditional subcases** and
historical Lean repairs, NOT a full proof/disproof.

## A. Prior main proof integration finalized

Three previously pending workflows for the main WIP incorporating
the `m + r <= 8` no-top/next-layer cardinality criterion
**completed successfully** on commit
`927268513e47e3a729a94c2122d3d107fc2f315a`:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39032577196
- https://github.com/Charlie-Wang-03/awards/actions/runs/39032577144
- https://github.com/Charlie-Wang-03/awards/actions/runs/39032577133

The next full Fast Incremental Lean run
https://github.com/Charlie-Wang-03/awards/actions/runs/39032577159
failed with **256 historical error diagnostics** across legacy
optional modules. This was not 256 mathematical admitted theorems.

## B. New sharp dyadic theorem: two exponent levels below the top

New file:
`JSP000404Research/SixteenCentreNoTopTwoLayerCountCapacity.lean`.

For any finite original exponent profile with `n>=4`,
`k(i)<=n-2` for every centre, let:
- `m=Fintype.card V`;
- `r=card {i | k(i)=n-2}`;
- `q=card {i | k(i)=n-3}`.

For all other centres `k(i)<=n-4`. In exact dyadic units,
`sum_i 2^k(i) <= (m+3*r+q) * 2^(n-4)`.
Hence the **explicit** criterion `m+3*r+q<=16` implies the
original target `sum_i 2^k(i)<=2^n`.

The file includes:
- `dyadic_capacity_of_no_top_two_layer_count_tradeoff`;
- `planar_no_top_two_layer_count_tradeoff_capacity`.

The second theorem is for **actual finite planar, injective,
AngleCap** data and real `CentreProjectiveCycle` exponents.
It deduces `k(i)<=n-2` from the previously kernel-proved
`centreExponent_lt_n` **and the extra hypothesis that no
centre has exponent n-1**. The weighted count `m+3*r+q<=16`
is an additional explicit profile premise, not a consequence
established for arbitrary planar AngleCap sets.

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39034549513:
**SUCCESS**, 3226 Lake jobs; `#print axioms` of both theorems
exactly `[propext, Classical.choice, Quot.sound]`.
No `sorryAx`. First-run arithmetic normalization was repaired
with `ring` and then recompiled successfully.

Main root
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
now dispatches this **wider** two-level no-top count criterion
before the older `m+r<=8` case and uniform-drop case.
Root insertion commit:
`9d7c435b8ccc935f91cd45e41d2e5786fb95e21a`.
Exactly ONE executable old `sorry` remains (line 745 after
insertion) for the actual global six-source nonreusable payment.
New focused integration runs:
- https://github.com/Charlie-Wang-03/awards/actions/runs/39034812381
- https://github.com/Charlie-Wang-03/awards/actions/runs/39034812351
- https://github.com/Charlie-Wang-03/awards/actions/runs/39034812310

These runs had not returned their final conclusions at the
moment this checkpoint was drafted. Do NOT infer integration
success from standalone capacity CI.

## C. Historical Lean fix #1: sharp support-two large angles

File `JSP000404Research/SharpSupportTwoLargeAngle.lean`
had five historical diagnostics on full incremental CI. Both
theorem binders introduced a phantom `lam` because the
`AngleCap p lam` binder appeared before the explicit
`{lam t delta : Real}` parameters. Reordering bound these
to the SAME lambda and repaired all five downstream type
and inequality failures without changing either conclusion.

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39034242777:
**SUCCESS**, 3464 Lake jobs; both printed axioms exactly
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`.

## D. Historical Lean fix #2: deficit-three support-one geometry

File `JSP000404Research/DeficitThreeSupportOneGeometry.lean`
had seven historical diagnostics. The original reference to
`exists_oneSupportIntervalCertificate` was obsolete.
The current `ConcreteOneSupportInterval.lean` actually
supplies `concrete_one_support_interval_certificate`,
which we unpacked to get one positive transition quotient,
a geometric common-signed interval, its exact width, and
actual radial ray representations.

The repaired proof derives the angle bound DIRECTLY using:
- `angle_positive_smul_signedRay`;
- `angle_signedRayDirection_eq_of_sign_eq`;
- the absolute parameter difference bound by interval width.

Other repairs fix opposite-vertex inequalities, the planar
triangle angle orientation, and `Nat.cast_sub` cast equalities.
The original three mathematically meaningful theorem
statements remain intact.

Focused CI https://github.com/Charlie-Wang-03/awards/actions/runs/39034738574:
**SUCCESS**, 3249 Lake jobs, all three printed axioms exactly
`[propext, Classical.choice, Quot.sound]`. NO `sorryAx`.

Combined newly kernel-certified historical repairs: **12
diagnostics** across two independent legacy Lean modules.
This count is not a fresh full-tree build count.

## E. Remaining open global obligation

Original JSP-000404 still has no complete proof or counterexample.
The unique admitted main lower-branch proof requires a global
ACTUAL retained-edge six-source allocation. It must cover:
mobile/soft bridge liabilities, hard/terminal twin/mixed carriers,
NET duplicate debt, covered blockers and projected profile loss,
using only LITERAL TRUE external Boolean holes and genuinely
UNRESERVED dyadic surplus, without reusing either resource.
Conditional profile cuts and independently certified local
matching/slot bounds do not establish that global payment.

No new `sorry` or custom mathematical axioms were intentionally
introduced; the original intentional WIP `sorry` is still visible.
