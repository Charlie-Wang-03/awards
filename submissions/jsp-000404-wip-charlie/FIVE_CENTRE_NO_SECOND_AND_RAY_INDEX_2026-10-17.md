# JSP-000404 — five-centre no-second-layer proof and canonical-ray-index repair

Date: 2026-10-17
Repository: Charlie-Wang-03/awards
Research branch: research/jsp-000404-sharp-centre

## A. New genuine planar geometric dyadic-capacity subcase

Source: `JSP000404Research/FiveCentreNoSecondLayerCapacity.lean`.

Theorem:
`planar_five_centre_no_second_layer_capacity`.

Under the actual finite injective planar `AngleCap p lam` hypotheses, with
`3 <= card V <= 5`, `n >= 3`, `0 <= delta < 1/2`,
`t = n + delta`, `lam = pi/t`, actual cycles `C`, a fixed actual
centre `s` of exponent `n-1`, and **no actual centre of exponent
`n-2`**, the original dyadic target
`sum_i 2 ^ centreExponent(C i) t <= 2 ^ n` is PROVED.

Proof: existing genuine planar top uniqueness forces all other exponents
to be at most `n-3`; there are at most four others and
`2^(n-1) + 4*2^(n-3) = 2^n`. No abstract payment assumption is used.
The no-second-layer condition is a **real additional hypothesis** and is
NOT derivable from `AngleCap` by any theorem here.

Arithmetic supporting theorem:
`dyadic_capacity_of_top_and_four_low`.

Focused CI run:
https://github.com/Charlie-Wang-03/awards/actions/runs/39025029436
**SUCCESS**, 3499 Lake jobs, source at
`7f28fdae86a0f24be74fe3b9508d8a14abaefdc6`.
The `#print axioms` lists for BOTH new theorems are exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

## B. Main admitted theorem narrowed to exclude this new subcase

Source: `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`.

Previously the proof discharged the already verified <=2, 3-centre,
and 4-centre original planar cases before using ONE admitted
global six-source payment. It now additionally splits on the
**actual five-centre/no-second-layer/top-centre** hypothesis and
proves its positive branch using theorem A and the established
`angleCap_reindexedPoint` bridge. The negative branch retains the
same ONE admitted payment `sorry`. This is an actual restriction of
the outstanding sorry domain, not the full solution.

Admitted-root focused CI verification was launched:
https://github.com/Charlie-Wang-03/awards/actions/runs/39025213483
Status at documentation draft: PENDING; do not infer kernel success
from merely submitting the source. The sibling preexisting focused
workflows also began on the WIP source update.

## C. Historical Lean compilation repair

Source: `JSP000404Research/CentreRayIndex.lean`.

Fixed the `List.Nodup.getEquivOfForallMemList` argument list;
replaced fragile list-get cancellation by the actual equivalence's
injectivity; explicitly rewrote indexed ray getters in theta-order
proofs.

Focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/39025320307
**SUCCESS**, 3210 Lake jobs, source at
`f8a6560d79139f8f67491856b76b3c54be4ccf2e`.
All printed axioms in that module are exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

## D. Boundaries and remaining obligations

* Original JSP-000404 is NOT completely proved or disproved.
* The ONE executable `sorry` remains in
  `PlanarLowerBranchProofAdmittedWIP.lean`. Its physical line number
  shifted from 647 to 663 after inserting the new closed branch.
* The unsolved mathematics is the actual global six-source payment:
  a nonreusing allocation of covered translated-loss blockers,
  cross-coordinate duplicates, terminal twin/mixed/soft/mobile debts
  into true *external* holes and genuinely unreserved surplus.
* The latest observed full Fast Incremental Lean on the pre-continuation
  SHA `ea3809d1099207945252ea5ea289333834944fee` failed with
  414 individual Lean error diagnostics across historical modules.
  The current source already repairs `CentreRayIndex` separately.
  A dedicated successful focused CI is not a claim that the full root
  is error-free.
* Do not import a comb-only extremizing profile as an unsupported
  generic geometric theorem, double-count holes, or replace the final
  inequality by an equivalent unproved condition.

