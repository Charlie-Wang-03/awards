# JSP-000404 — exact Boolean-word multiplicity and geometric repair checkpoint (2026-10-16)

Branch: `research/jsp-000404-sharp-centre`.

**Research status: OPEN.** The original planar lower-branch capacity
proof has NOT been completed or disproved. File
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean`
still has its single executable `sorry)` at line 632.
No new admitted axiom, `sorry`, or other concealed proof shortcut
was introduced to certify the results listed below.

## 1. Exact per-word projected-loss multiplicity

Modules:
- `ResidualLossWordMultiplicityLedger.lean`
- `ResidualLossWordMultiplicityCoverSplit.lean`

For each Boolean word `w`, define `m(w)` as the number
of **distinct** chosen translated-loss coordinate slices `T_c`
that contain `w`. Let `U = ⋃_c T_c`,
`K = coveredCompletionWords C` be the actual originally
covered word set. These are ORIGINAL project-defined objects.

Certified identities:

```text
D_dup = Σ_(w∈U) (m(w)-1)
      = Σ_(w∈U∩K) (m(w)-1)
        + Σ_(w∈U\K) (m(w)-1).
```

The scoping of natural subtraction `m(w)-1` INSIDE
`Finset.sum` is explicit. It was required to correct a
failing Lean elaboration/tactic goal; it does not alter the
mathematical intent of the original multiplicity ledger.

Certificates:
- focused CI **38841390341 SUCCESS**, 3,308 targets, declaration
  `translatedLossDuplicateDebt_eq_sum_wordMultiplicity_excess`;
- focused CI **38841390165 SUCCESS**, 3,311 targets, declaration
  `translatedLossDuplicateDebt_eq_word_excess_covered_plus_trueHole`;
- checked `#print axioms` for both contains ONLY
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

The previously certified exact first-occurrence / genuine retained-edge
triple-index decomposition of `D_dup` is independently available.
Both index systems describe the SAME exact debt: the edge-index
accounting identifies the concrete source/blocker geometry; the
word-index accounting records repeated use of each actual Boolean word.

## 2. Exact terminal payment equivalence

Module:
`ResidualTerminalTwinWordMultiplicityPayment.lean`.

Certified theorem:
`terminalTwinSixSourcePayment_iff_wordMultiplicity_coverSplit`.

Focused CI **38841936276 SUCCESS**, 3,396 targets.
Axioms only `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`.

The ORIGINAL terminal six-source numerical inequality holds
**IFF** there exists a retained-active flip choice paying

```text
terminalTwinOtherFiveDebt
 + |true actual-colour covered-blocker union|
 + Σ_(w∈U∩K) (m(w)-1)
 + Σ_(w∈U\K) (m(w)-1)
 ≤ |global true holes OUTSIDE U|
   + genuinely UNRESERVED dyadic surplus.
```

This is a two-way **reformulation**, NOT proof of the
existential global payment inequality. Specifically,
`U\K` consists of true holes INSIDE U and therefore
cannot be double-credited as right-hand OUTSIDE-U resources.
Covered duplicate words `U∩K` are not holes.
No global matching or injection between these demands and
valid external resources has been established.

Integration into the independent sorry-free
`VerifiedOverlapRewire.lean` root: focused CI
**38841832824 SUCCESS**, 3,592 targets.

## 3. Geometry: middle-hidden reverse-angle cluster separation

Module `MiddleHiddenClusterSeparation.lean`.

Previous calls to `EuclideanGeometry.angle_le_angle_add_angle`
were oriented the WRONG way for deriving a lower angle bound.
The certified correction uses
`angle(top,r) ≤ angle(top,b)+angle(b,r)` and
`angle(top,d) ≤ angle(top,c)+angle(c,d)`.

With long top/r and top/d gaps both `>(1+δ)λ`,
and short r/b + c/d mass `≤δλ`, these imply
`angle(top,b)>λ` and `angle(top,c)>λ`.

Focused CI **38841285581 SUCCESS**, 3,205 targets.
`middle_hidden_cluster_separation` has axioms only
`[propext, Classical.choice, Quot.sound]`.

## 4. Other certified repairs

- `CanonicalRankMiddleTerminal.lean`: corrected classic
  decidability in the `canonicalRank` definition and the strict
  rank-growth proof. Focused CI **38840267050 SUCCESS**,
  3,211 targets; `canonicalRank_lt_of_lt`,
  `canonicalRank_add_two_le_of_chain`,
  `no_two_middleHiddenRankSignatures` all no `sorryAx`.
- `ListPositiveMemberBound.lean`: repaired the zero-quotient
  case without losing its equality witness during substitution.
  Focused CI **38841518427 SUCCESS**, 3,094 targets.
  `positive_member_le_n_sub_two_of_support_three_sum`
  proves `q ≤ n-2` whenever `q>0`, positive support 3,
  and total quotient sum n; no `sorryAx`.

Further under verification: shared ray-sign reversal lemma moved
to `CanonicalRaySignOrder.lean`; `MiddleHiddenCanonicalRankBand.lean`
now uses the same upstream lemma as `MiddleHiddenRankBridge.lean`;
`PositiveTransitionAngleAlignment.lean` imports the actual
`CentreSignPath` and uses nonempty-list last-element membership.
The latest middle-hidden joint focused CI must be checked independently;
its outcome is not presumed successful in this checkpoint.

## 5. Open frontier and compilation limitations

A prior Fast Incremental Lean run on the research branch
(38775236970) **FAILED** with 388 error diagnostics across 49
historical Lean modules. The focused successes above do not
establish a full-workspace green build. Subsequent fast runs
may have been cancelled or still executing.

The remaining actual JSP-000404 proof obstacle is the GLOBAL
non-reuse/payment inequality. Exact word multiplicities and
genuine edge carriers are now established, but it is not
proved that the planar `AngleCap` hypotheses force sufficient
true Boolean holes OUTSIDE translated loss `U`, together
with genuinely unreserved surplus, to pay all debt classes.
There is no claim of an unconditional proof or counterexample.
