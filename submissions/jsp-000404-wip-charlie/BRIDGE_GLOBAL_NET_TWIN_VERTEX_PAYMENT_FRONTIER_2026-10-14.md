# JSP-000404 — Global NET/TWIN original-vertex budget and planar dyadic liability

Research date: 2026-10-14.
Branch: `research/jsp-000404-sharp-centre`.
Status: **partial mathematical progress only**. Full JSP-000404 open; the one admitted six-source global payment `sorry` in `PlanarLowerBranchProofAdmittedWIP.lean` remains.

## Independently kernel-checked mathematics

### A. Any number of original vertices (verified)

If the exact actual NET collision source-to-diagonal map has positive duplicate debt
`E_D > 0`, and `T` is the collection of actual terminal equal-exponent TWIN
rigid hard carriers, then

    8 + 2 * |T| <= |V|.
    Equivalently |T| + 4 <= floor(|V| / 2).

This is derived from a SAME-TARGET pair of distinct actual NET sources.
The pair requires exactly four distinct hard carriers (two forward, two
strict reverse), all disjoint from TWIN carriers. The union injects into
the single matching of actual original HARD carrier pairs. This does
**not** falsely add the costs of sources with DIFFERENT target diagonals.

Lean modules:
- `ResidualNetCollisionTwinGlobalVertexBudget.lean`
  - `net_collision_positive_duplicate_twin_global_vertex_budget`
  - `net_collision_positive_duplicate_twin_card_plus_four_le_half`
- `PlanarNetGlobalTwinBudget.lean`
  - `planar_net_global_duplicate_or_twin_vertex_budget`

Actual focussed CI (explicit targets, no root umbrella):
https://github.com/Charlie-Wang-03/awards/actions/runs/38560021641

Result: **SUCCESS**, 3,473 jobs. All 3 theorem axiom audits:
`[propext, Classical.choice, Quot.sound]`; NO `sorryAx`.

### B. True planar AngleCap at most eleven centres (verified)

For real projected planar AngleCap configurations, `|V|<=11`,
and positive actual `E_D`, the previously proved carrier cardinal cap
`|T|<=1` combines with geometric `k(v)<n` to yield

    SUM_(p in T) 2 ^ k(p.second) <= 2 ^ (n-1).

This is a dyadic **liability cap**, NOT newly unreserved surplus.

Lean modules:
- `ResidualNetCollisionElevenCentreTwinMass.lean`
  - `net_collision_positive_duplicate_eleven_centres_twin_mass_le`
- `PlanarNetElevenCentreTwinMass.lean`
  - `planar_net_eleven_centres_duplicate_or_twin_mass_le`

Focussed CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38560808223

Result: **SUCCESS**, 3,473 jobs; both `#print axioms` contain only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

### C. Simultaneous target fibre/TWIN budget (VERIFIED)

In `ResidualNetCollisionTwinAdjustedFibre.lean` the REAL target fibre
and the actual TWIN hard carrier family consume one shared
original-vertex matching:

    4 * |F_d| + 2 * |T| <= |V|    for EVERY target d.

This gives the exact capacity and global finite target ledger:

    |F_d| <= floor((|V| - 2*|T|)/4);
    E_D <= SUM_(d in distinct actual diagonal image)
                 (floor((|V| - 2*|T|)/4) - 1).

All arithmetic is natural-number arithmetic, with truncated subtraction.
The pointwise bound is strictly more informative than a vertex-quarter
cap when extra TWIN hard carrier ownership reduces available vertices.

Independent focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38561321399

Result: **SUCCESS**, 3,471 jobs. Three newly proved declarations:
- `net_collision_fibre_twin_joint_vertex_budget`
- `net_collision_fibre_card_le_twin_adjusted_quarter`
- `net_collision_duplicate_debt_le_twin_adjusted_quarter_excess`

All 3 `#print axioms`:
`[propext, Classical.choice, Quot.sound]`, NO `sorryAx`.

### D. Target-exact coloured-slot matching with TWIN vertex reservation (VERIFIED)

`ResidualNetCollisionTwinMatchingJointPayment.lean` proves:

    |F_d| <= min(nu_coloured_slot(G_d), floor((|V|-2*|T|)/4)).

It transports this source-fibre cap into the exact NET duplicate-image
debt sum and actual mobile hard-source ledger, preserving the TRUE
Boolean holes vs already-COVERED target blocker distinction.

Focused Lean CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38562709753

Result **SUCCESS**: 3,472 jobs, 4 audited declarations;
axioms are exactly [propext, Classical.choice, Quot.sound].

### E. Source-native ORIGINAL bridge matching with TWIN reservation (VERIFIED)

**New theorem:** `ResidualNetCollisionOriginalTwinJointCapacity.lean`.
With `mu_original(d)` the maximum number of eligible SOFT
target-exact bridges using pairwise vertex-disjoint ORIGINAL centres,
not merely separate coloured endpoint slots:

    |F_d| <= min(mu_original(d), floor((|V|-2*|T|)/4)).

This is independently formally established **no weaker than BOTH**:
- `min(nu_coloured_slot(d), floor((|V|-2*|T|)/4))`
- `min(mu_original(d), floor(|V|/4))`

The exact diagonal-image excess sum and mobile source budget inherit
the stronger bound. The full mobile bound continues to track actual
singleton words, actual soft words, literal Boolean holes, distinct
already-COVERED diagonal blockers, and duplicate-image excess separately.

Kernel-checked declarations:

- `net_collision_fibre_original_matching_twin_reserved_min`
- `net_collision_original_twin_min_le_slot_twin_min`
- `net_collision_original_twin_min_le_original_quarter_min`
- `net_collision_duplicate_debt_le_original_twin_matching_excess`
- `net_mobile_mass_le_holes_covered_original_twin_matching_excess`

Focused GitHub Actions CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38578187635

Result **SUCCESS**, 3,473 jobs, zero Lean errors.
All five #print axioms checks:
[propext, Classical.choice, Quot.sound]. NO sorryAx.

The improvement is a pointwise bound on ACTUAL source fibres, not a
claim of globally non-reusable targetwise carrier or true-hole payments.
Even if the new bound is strictly smaller for a target, that alone does
not prove global six-source dyadic capacity, since soft, twin,
mixed-rigid and projected profile loss liabilities remain outstanding.


### F. Root import-chain repairs without introducing proof holes

Historical root entry `JSP000404Research.lean` remains NOT green. The
full fast CI contains many unrelated legacy errors; separate certified
frontier modules MUST NOT be downgraded because of those errors, and
neither should they be presented as a fully green root tree.

An actual **logical prerequisite** was repaired in
`BinaryMissingDefect.lean`: an old tactic step tried to infer

    |V| + |Q| <= 2^k

from `|Q| <= D` and `D <= 2^k - |V|` using Nat truncated
subtraction WITHOUT first establishing `|V|<=2^k`.
The correct proof derives the missing baseline capacity from
`weighted_hansel bit specified hsep`, then uses the truncated defect
inequality. No new mathematical assumption, sorry or axiom is added.

Focused CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38580323522

Result: **SUCCESS**, 3,095 jobs, zero Lean errors;
`weighted_hansel_missing_finset` and its two
`BinaryEdgePartition` corollaries are kernel-checked and free of
`sorryAx`.

A stale Mathlib import `Mathlib.Data.Matrix.Notation` in
`SupportIntervalCertificate.lean` was replaced with
`Mathlib.Data.Matrix.Basic`. This fixes the observed invalid import,
but the independent support-interval run
https://github.com/Charlie-Wang-03/awards/actions/runs/38580724431
has now completed **FAILURE**. It exposed six previously masked
elaboration errors in dependency `ConcreteTransitionInterval.lean`
(lines 81, 121-122, 226, 279 and 307), including an AngleCap
`lam` parameter mismatch, removed `List.length_eq_zero.mp`,
list-expression rewrite shape drift, and a wrong
`div_pos_iff` branch elimination. `SupportIntervalCertificate.lean`
itself is therefore NOT yet kernel-verified at the new HEAD.
Do not represent this chain as repaired or the root umbrella as green.


## Integrity and outstanding geometric obligation

1. Local source-fibre multiplicity, hard carrier matching and TWIN dyadic
   upper bounds count ACTUAL objects. They are **not** non-reusable Boolean
   hole credits or unused dyadic profile surplus.
2. Full six-source payment still has true Boolean hole vs ALREADY COVERED
   diagonal distinctions, fifth-centre blockers, soft overlap,
   terminal TWIN mass, both mixed-rigid classes and projected loss.
3. Different target fibres can reuse original carriers; summing raw
   per-target vertex consumption is invalid without a disjoint-allocation
   theorem. The above results do not make that erroneous step.
4. `JSP000404Research.lean` imports a large HISTORICAL umbrella collection
   with hundreds of unrelated elaboration failures. It is NOT fully green.
   Keep isolated kernel-verified frontier separate from historical root
   compilation debt, and do not claim an unrestricted proof.

## Next non-admitted mathematical proof

Prove a geometry-correct, genuinely GLOBAL non-reusing payment assignment
from actual collision sinks (and separately terminal rigid/mixed/soft/loss
liabilities) into literal TRUE Boolean holes and dyadic surplus proven
UNRESERVED by all prior carrier allocations. Work with distinct actual
targets and fifth-centre blocker witnesses; do not equate a bound on
candidate bridge/matching capacities with payment.


## 2026-10-14 continuation: unrestricted dyadic twin cap and isolated Lean repair

### F. Arbitrary-size dyadic TWIN liability (kernel-verified)

`ResidualNetCollisionGlobalTwinDyadicLiability.lean` combines the
earlier **verified**, genuinely same-target NET duplicate witness
vertex budget `8 + 2*|T| <= |V|` with the exponent bound:

When actual duplicate debt `E_D > 0` and all exponents satisfy
`k(v) < n`, the total TWIN dyadic **liability** is bounded by

    SUM_(p in TWIN) 2 ^ k(p.second)
      <= (floor(|V|/2) - 4) * 2^(n-1).

The weaker non-strict bound uses `2^n`. The conditional theorem
`E_D = 0 OR (strict liability cap)` is also verified.

`PlanarNetGlobalTwinDyadicLiability.lean` proves the corresponding
TRUE planar AngleCap statement without any |V| <= 11 condition.

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38583820034
SUCCESS: 3,474 Lean jobs, zero errors; all four new theorem axioms
[propext, Classical.choice, Quot.sound], no sorryAx.

### G. Source-fibre-specific weighted TWIN tradeoff (CI pending)

Proposed abstract and genuine planar `AngleCap` theorem:

    forall ACTUAL target d,
    SUM_(p in TWIN) 2 ^ k(p.second)
      <= (floor(|V|/2) - 2*|F_d|) * 2^(n-1).

This refines the positive-duplicate bound when one fixed target has
more than two actual NET sources, but does NOT spend vertex or soft
bridge payment again at other targets. Source:

- `ResidualNetCollisionTwinFibreDyadicTradeoff.lean`
- `PlanarNetTwinFibreDyadicTradeoff.lean`

Focused CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38584349299
**Do not mark verified before successful kernel checks and axiom audit.**

### H. Restored old local Lean chain (independent CI verified)

Targeted geometry and Hansel modules, formerly failing downstream of
stale Mathlib imports and dependent Fin-4 sum elaboration, now compile
independently with no sorryAx in audited declarations.

- Support interval:
  https://github.com/Charlie-Wang-03/awards/actions/runs/38584726476
  SUCCESS (3,441 jobs), including the genuine
  `four_turnLength_sum_le_two_pi` theorem.
- Transition interval:
  https://github.com/Charlie-Wang-03/awards/actions/runs/38584726192
  SUCCESS (3,441 jobs).
- Weighted Hansel missing-vertex defect:
  https://github.com/Charlie-Wang-03/awards/actions/runs/38584726284
  SUCCESS (3,445 jobs).

**DO NOT CONFLATE THESE RESULTS WITH FULL ROOT COMPILATION OR WITH
THE MISSING UNRESTRICTED SIX-SOURCE GLOBAL NON-REUSED PAYMENT.**


## Continued formalization: cross-target SOFT shadow multiplicity (2026-10-14)

### I. Global SOFT-shadow reuse incidence (CI not yet certified)

Proposed Lean source:
`JSP000404Research/ResidualNetCollisionGlobalSoftShadowReuse.lean`.

For any finite set D of Boolean diagonals, with S the ACTUAL
softOverlapCompletionWords, define H(d,s) to mean Hamming(d,s)=2.
The exact global double-counting identity is

  SUM_(d in D) #{s in S : H(d,s)}
    = SUM_(s in S) #{d in D : H(d,s)}.

Unlike target-by-target SOFT cardinal inequalities this counts the
precise extent to which one covered SOFT shadow is reused by DIFFERENT
targets. No global pairwise disjointness is assumed. Combining with
the existing exact actual NET fibre duplicate ledger yields the proposed

  actual E_D <= SUM_(s in S) #{d in D_actual : H(d,s)}.

This is a COVERED SOFT shadow incidence bound, not payment by unique
true holes, and not proof that these SOFT words are unreserved.

Focused run:
https://github.com/Charlie-Wang-03/awards/actions/runs/38589790783
Do not claim it passed until the job reaches SUCCESS and the
`#print axioms` lines exclude `sorryAx`.

### J. Bounded global SOFT-shadow reuse per fixed word (CI not yet certified)

Proposed Lean source:
`JSP000404Research/ResidualNetCollisionShadowReuseMultiplicityCap.lean`.

Fix s. The exact Hamming-two difference set of d relative to s
uniquely determines d, and it is a two-element subset of Fin n.
Consequently

  #{d in D : H(d,s)} <= Nat.choose n 2.

Together with I this would yield a GLOBAL non-fictitious multiplicity
bound on genuine duplicate-image debt:

  E_D <= Nat.choose n 2 * |S|.

The factor is explicitly retained; the statement NEVER says
|D| distinct target sinks inject directly into |S| SOFT words.
This bound by itself does not settle Boolean-hole or unreserved
profile surplus payment.

Focused run:
https://github.com/Charlie-Wang-03/awards/actions/runs/38590448333
Pending successful kernel and axiom audits.

### K. Two root-import dependency repairs (verified)

The historical root umbrella still fails because of many other stale
modules; the two scoped modules below ARE actually verified:

- `StableDeletionReduction.lean`: restored decidable finite erase
  and explicit disjoint partition proof.
- `TransitionCutExposure.lean`: corrected theorem application
  argument positions for Bool sign and ray representation.

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38589909740
SUCCESS, 3,209 Lake tasks, zero Lean errors, six
`#print axioms` with only [propext, Classical.choice, Quot.sound].

### Next exact global payment frontier

The local target exact-shell matching, TWIN-reserved original-vertex
capacity, and bounded SOFT shadow reuse are capacity constraints.
To close the existing single admitted global six-source theorem one
needs a NEW geometry-derived disjoint allocation of actual covered
target blockers / duplicate excess / TWIN / both mixed-rigid / SOFT
and projection loss liabilities to genuinely available TRUE Boolean
holes and **UNRESERVED** dyadic surplus. Source incidence multiplicity
is not an injection to spendable credits.

No existing `sorry` or theorem statement has been altered, and no
additional axiom has been introduced.


## 2026-10-15 continuation: verified cross-target SOFT reuse

**Verified original research:** `ResidualNetCollisionGlobalSoftShadowReuse.lean` and `ResidualNetCollisionShadowReuseMultiplicityCap.lean` now both kernel-check in [CI #38597062511](https://github.com/Charlie-Wang-03/awards/actions/runs/38597062511). Build: SUCCESS (3,282 jobs, zero errors). All four printed theorem axiom sets are exactly `[propext, Classical.choice, Quot.sound]` and contain no `sorryAx`.

Let `D = netCollisionCertifiedDiagonalWords C exponent hexp honeLoss` and `S = softOverlapCompletionWords C`. For an ACTUAL soft word `s`, its target reuse multiplicity `m(s)` is the number of `d ∈ D` differing from `s` in exactly two Boolean coordinates. Lean establishes:

```text
SUM_(d in D) |targetHammingTwoSoftOverlapWords C d|
  = SUM_(s in S) m(s),
E_D <= SUM_(s in S) m(s),
m(s) <= Nat.choose n 2,
E_D <= |S| * Nat.choose n 2.
```

This faithfully counts all possible **cross-target shadow reuse**. It is an upper bound on COVERED resources, not an injective true-hole payment or proof of any unreserved dyadic surplus. The bound can be looser than some prior target-specific matching bounds; it is valuable for accounting for reuse explicitly, not as an automatic strict improvement in the original theorem.

**Verified historical Lean repair:** `MinimalPhaseCover.lean` previously had three opposite-direction inequality witnesses (`i ≠ j` vs `j ≠ i`). Their corrected uses kernel-check in [CI #38597418973](https://github.com/Charlie-Wang-03/awards/actions/runs/38597418973): SUCCESS (3,092 jobs, zero errors); audited theorems depend only on standard Lean logical axioms.

**Additional strict first-hit target obligation (PENDING):** `ResidualNetCollisionShadowFirstHitGlobalCharge.lean`, independent [CI #38598066535](https://github.com/Charlie-Wang-03/awards/actions/runs/38598066535), proposes the stronger bound `E_D + |D| <= SUM_s m(s)`, using exact finite-map first-preimage accounting. Do not count as proved until the CI is SUCCESS and its axiom audit is clean.

The only intentionally admitted global six-source proof `sorry` in `PlanarLowerBranchProofAdmittedWIP.lean` is untouched. The historical root entry still has unrelated compile errors; isolated successful CIs do NOT make the entire root green.


## 2026-10-15: first-hit global NET/SOFT accounting and historical repair

### Kernel-verified global first-hit shadow incidence ledger

`ResidualNetCollisionShadowFirstHitGlobalCharge.lean` was independently checked in [CI #38598066535](https://github.com/Charlie-Wang-03/awards/actions/runs/38598066535): SUCCESS, 3,282 jobs, zero errors. Both audited theorems use only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The theorem `finite_image_duplicate_plus_first_hits_le_fibre_caps` is a generic exact finite-fibre source capacity inequality. Its real NET specialization proves, with D the set of DISTINCT ACTUAL diagonal targets and S the set of ACTUAL covered SOFT overlap completion words,

```text
E_D + |D| <= SUM_(s in S) #{d in D : Hamming(d,s)=2}.
```

Unlike the prior bound on E_D alone, this retains exactly one **first source** per hit target as a charge, with remaining source mass counted as actual duplicate-image excess. The shadow incidence sum still counts REUSE and is entirely COVERED; it must NOT be treated as true-hole credit.

The refinement combining this inequality with the verified per-shadow `Nat.choose n 2` degree cap has been committed as `net_duplicate_plus_distinct_hits_le_choose_soft_mass` and has focused CI [#38599220607](https://github.com/Charlie-Wang-03/awards/actions/runs/38599220607). **Do not claim this refined theorem verified until its CI succeeds.**

A true planar `AngleCap` adaptation of the first-hit plus choose bound is committed as `PlanarNetGlobalSoftFirstHitReuse.lean`, [focused CI #38599457731](https://github.com/Charlie-Wang-03/awards/actions/runs/38599457731), also **PENDING**.

### Newly isolated true-hole refund (NOT YET VERIFIED)

`ResidualNetCollisionTrueHoleRefundShadowLedger.lean` uses the certified target decomposition

```text
|D| = |D ∩ TRUE HOLES| + |D ∩ ALREADY COVERED|.
```

Combining the existing honest mobile hard-source ledger with the new first-hit shadow incidence inequality proposes the more geometrically meaningful bound

```text
mobile hard mass <= singleton covered mass + soft covered mass
                  + (all TRUE holes - already NET-hit TRUE holes)
                  + SUM_(s in S) #{d in D : Hamming(d,s)=2}.
```

This eliminates the separately charged COVERED diagonal blocker term and refunds NET-hit true holes from the available-hole account. It does **NOT** convert SOFT shadow incidence into unreserved payment. Dedicated CI [#38599828846](https://github.com/Charlie-Wang-03/awards/actions/runs/38599828846) is **PENDING**; only promote after kernel and axiom verification.

### Historical Lean source repairs (independently verified)

- `MinimalPhaseCover.lean`: corrected three inequality witness direction errors; [CI #38597418973](https://github.com/Charlie-Wang-03/awards/actions/runs/38597418973), 3,092 jobs SUCCESS, zero errors, no sorryAx.
- `LinearArcPacking.lean`: repaired empty-list base and tail-sum normalization; [CI #38598375567](https://github.com/Charlie-Wang-03/awards/actions/runs/38598375567), 3,092 jobs SUCCESS, zero errors, no sorryAx.
- `ResidualListCapacity.lean`: explicit classical decidable residual edge choice and typed compatibility premise; [CI #38598920727](https://github.com/Charlie-Wang-03/awards/actions/runs/38598920727), 3,098 jobs SUCCESS, zero errors, no sorryAx.
- `OneSupportTransitionCost.lean`: repaired zero-quotient branch, dependent `AngleCap` parameter, ray-list constructor and local Sendov scale inequality; [CI #38599086065](https://github.com/Charlie-Wang-03/awards/actions/runs/38599086065), 3,237 jobs SUCCESS, zero errors, no sorryAx.

**Open proof**: the single intentional global six-source payment `sorry` in `PlanarLowerBranchProofAdmittedWIP.lean` remains untouched. These verified improvements do not establish a non-reusable global allocation of SOFT, TWIN, mixed-rigid and projection-loss liabilities to available true holes and genuinely unreserved profile surplus. The historical root umbrella is still not fully green.
