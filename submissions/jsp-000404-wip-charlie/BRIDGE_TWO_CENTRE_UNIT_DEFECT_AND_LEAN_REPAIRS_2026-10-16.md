# JSP-000404 — Two-centre unit-defect rigidity and targeted Lean repairs

Date: 2026-10-16. Branch: `research/jsp-000404-sharp-centre`.

**Mathematical status: OPEN.** This checkpoint is not a complete
proof or disproof of JSP-000404. The original planar root still has
one executable `sorry` in
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`, at
approximately line 632. It is the genuine *global non-reusing* payment
of terminal debts by true Boolean holes outside the translated-loss
union and truly unreserved surplus. All new results below preserve
the original definitions and introduce no custom axioms or admissions.

## 1. Quantitative one-unit necessary condition for a deficient pair

The existing verified
`ResidualTwoVertexDeficiencySlack.lean` result says that for any
distinct two-centre enlarged Hall-deficient core under the original
one-layer assumptions, with retained completion cubes `Q_v,Q_w`
and target masses `d_v=2^exponent(v)`,
`d_w=2^exponent(w)`:

```text
|Q_v ∩ Q_w| + d_v + d_w > |Q_v| + |Q_w|.
```

The new
`JSP000404Research/ResidualTwoVertexUnitDefect.lean` proves two
further statements:

* `two_vertex_enlarged_deficiency_unit_intersection_rigidity`
* `two_vertex_enlarged_not_deficient_of_unit_intersection_slack`

If the original retained completion cubes have intersection
cardinality **at most one**, actual pair deficiency forces
`|Q_v|=d_v`, `|Q_w|=d_w`, `|Q_v∩Q_w|=1` and the exact one-word
deficit

```text
|Q_v ∪ Q_w| + 1 = d_v + d_w.
```

Consequently one strictly nonsaturated cube forbids a deficient pair
in this regime. These are **conditional structural results**: neither
a general geometric singleton-intersection bound nor absence of
three-or-more-centre cores has been proved.

**Focused CI:**
[38907698758](https://github.com/Charlie-Wang-03/awards/actions/runs/38907698758)
**SUCCESS**, 3,318 jobs. Axiom audit: only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

## 2. Certified repair: two small actual Euclidean angles

Module `JSP000404Research/TwoSmallAngleContradiction.lean`.

* Corrected the use of injectivity and vertex inequality orientation.
* Used the triangle angle-sum identity in its actual orientation and
  only commuted the third term as needed.
* Corrected the original `AngleCap` proof argument order.

All four original triangle-angle theorems are now kernel-checked,
including the contradiction when two triangle angles are each
bounded by `delta * lam` with `delta < 1/2`, while the global
angle cap is `pi - lam`.

**Focused CI:**
[38907893735](https://github.com/Charlie-Wang-03/awards/actions/runs/38907893735)
**SUCCESS**, 3,204 jobs, no `sorryAx` in the four declarations.

## 3. Certified repair: excess-compensated stable deletion

Module `JSP000404Research/StableDeletionExcess.lean`.

* Made the `DecidableEq V` instance explicit in the two statement
  signatures which construct a complement of finite vertex sets.
* Replaced an unavailable disjointness lemma with an explicit proof
  that the unstable set and its complement are disjoint.
* Verified the partition of total weight into unstable and stable
  parts; a malformed complement token in the first attempt was
  corrected before certification.

**Focused CI:**
[38908263860](https://github.com/Charlie-Wang-03/awards/actions/runs/38908263860)
**SUCCESS**, 3,095 jobs, all three audited declarations without
`sorryAx`. The decidability parameter is constructive/computational,
not a mathematical hypothesis on the planar configuration.

## 4. Additional targeted legacy repairs — subsequently CI-certified

* `ResidualThroughDensity.lean`: repairs the colour-cast injection
  argument and both empty boundary-palette proofs. The first focused
  run [38908710661](https://github.com/Charlie-Wang-03/awards/actions/runs/38908710661)
  failed on tactic-branch indentation; this was corrected. Latest
  verification: [38909092368](https://github.com/Charlie-Wang-03/awards/actions/runs/38909092368).
* `FourCentreSupportTwoContradiction.lean`: repairs sharp-ray
  distinctness orientation, geometry scale binders, the `2≤n`
  specialization, and triangle angle-sum use. First focused run
  [38908804915](https://github.com/Charlie-Wang-03/awards/actions/runs/38908804915)
  identified two further reversed sharp-ray inequalities, subsequently
  corrected. Latest verification:
  [38909150900](https://github.com/Charlie-Wang-03/awards/actions/runs/38909150900).

The focused workflows now have correctly spelled source-file path
filters; earlier versions accidentally replaced a path separator by a
dot, so source-only pushes did not trigger them.

## 5. Full-project state and remaining proof dependency

The baseline broad incremental workflow
[38905556681](https://github.com/Charlie-Wang-03/awards/actions/runs/38905556681)
failed with 375 Lean errors spread over 36 legacy modules.
Focused module success is NOT equivalent to a complete library build.
A fresh full error census is required after the targeted repairs.

The original full theorem still depends on a single **globally
non-reusing payment** across terminal twin, mixed-rigid, soft,
covered-loss-blocker and loss-duplicate obligations. The two-centre
unit-defect theorem narrows one local family of potential
counterconfigurations only; it does not construct outside true-hole
credits, reserve available surplus, or resolve larger Hall cores.

## 6. Prior-public-work check and statement integrity

Upstream [PR #2804](https://github.com/TheJustinSunPrize/awards/pull/2804)
advertises a complete Sendov formalization, but the linked pinned
`Yi-111-a/jsp-000404-blumenthal-sendov`
`lean/JSP404/Defs.lean` defines `alpha N` **directly as the
piecewise Sendov expression**. Its
`sendov_minimax_angle` proof only unfolds this definition and
normalizes the dyadic band index; it does not prove the original
geometric minimax formulation. Therefore this is not evidence that
the genuine geometry-to-formula theorem has been closed.

Do not replace the authentic plane-extremal quantity with its
conjectured final expression to eliminate the WIP proof debt.
Other external PRs still require individual scope review before any
claim about complete public priority or award eligibility.

**Next mathematical gate:** derive a genuine planar overlap/geometric
classification that excludes the remaining saturated singleton-defect
pair or pays its exact word cost, then extend the accounting to
three-plus-centre cores without reusing Boolean holes or surplus.

## 7. Confirmed follow-on focused CI outcomes (same day)

The two results previously recorded as pending in Section 4 have
now passed their own exact-source kernel builds:

**Residual through-colour density:**
[38909531761](https://github.com/Charlie-Wang-03/awards/actions/runs/38909531761)
**SUCCESS**, 3,123 jobs. The repaired
`residualThroughColours_card_le_left/right` injections and both
zero-exponent boundary theorems depend only on
`[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`
in those four declarations. Final source commit:
`e1161119106d8764a4fea51f734d66613b14eb5a`.

**Four-centre genuine geometry exclusion:**
[38909539248](https://github.com/Charlie-Wang-03/awards/actions/runs/38909539248)
**SUCCESS**, 3,252 jobs. The theorem
`no_sharp_with_two_support_two_deficit_two_fin_four` now
kernel-checks with only the three standard axioms. It excludes,
for a genuine injective four-point planar configuration satisfying
the stated `AngleCap` and normalized parameters, one
`n-1` sharp centre coexisting with two distinct `n-2`
quotient-support-two centres. This is a real geometric exclusion
of a small exceptional branch. It does NOT establish the full
arbitrary-cardinality planar lower bound or final global nonreuse
payment. Final source commit:
`04ebb1d752960446ca89ab220bc866e049cc4fb1`.

Both repaired modules preserve the original mathematical theorem
statements. In total, this checkpoint now references **five**
independent focused successful kernel checks (two-centre unit defect,
two-small-angle contradiction, stable deletion excess, residual
through-density, and four-centre support-two terminal).

The root `PlanarLowerBranchProofAdmittedWIP.lean` still has one
executable `sorry`. The full-workspace build is not certified green.
