# JSP-000404 — Exact first-occurrence duplicate debt and actual-edge dyadic upper budget (2026-10-15)

Research branch: `research/jsp-000404-sharp-centre`.
Original JSP-000404 proof/decision status: **OPEN**. The admitted
`PlanarLowerBranchProofAdmittedWIP.lean` still has one executable
`sorry`; none of the following results pays the global six-source
debt unconditionally.

## Certified exact first-occurrence identity

Module: `JSP000404Research/ResidualLossPairwiseOvercount.lean`.

- `lossPrefixUnion_inter_card_le_pairwise`
- `lossSumCard_le_prefixUnion_add_pairwise`
- `lossSumCard_eq_prefixUnion_add_priorOverlap`
- `lossSliceAtNat_sum_card_eq_fin_sum`
- `lossSliceAtNat_prefix_union_eq_loss_union`
- `translatedLossDuplicateDebt_le_pairwise_slices`
- `translatedLossDuplicateDebt_eq_sum_prior_coordinate_overlaps`

Focused CI **38756885932: SUCCESS** (3,310 jobs). The new
exact-duplicate theorem has axioms
`[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.

For a given actual chosen loss-coordinate slice `T_i`,
the unconditional identity is

```text
D_dup = Σ_(i<n) |T_i ∩ ⋃_(j<i) T_j|
      = Σ_(i<n) |T_i| - |⋃_(i<n) T_i|
      ≤ Σ_(j<i<n) |T_i ∩ T_j|.
```

All three terms are true finite Boolean-word sets from the original
`translatedLossDuplicateDebt` ledger, not a surrogate model.
A word present in m distinct slices contributes m-1 to D_dup.
The rightmost upper bound can overcount that word, but is never used
as an equality.

## Certified global dyadic envelope on true pairwise edge carriers

Module: `JSP000404Research/ResidualLossGlobalDuplicateDyadicBudget.lean`.

- `lossPairwiseActualEdgeDyadicCostAtNat` indexes only finite
  pairs `0 ≤ j < i < n`. Index pairs outside Fin n give zero.
- `translatedLossDuplicateDebt_le_actualEdge_dyadic_pairBudget`
  uses the certified pairwise theorem and certified
  `crossTranslatedLossSlice_inter_card_le_sum_min_dyadic`
  (earlier focused CI 38741614008).

Focused CI **38756672393: SUCCESS** (3,311 jobs).
Axioms `[propext, Classical.choice, Quot.sound]`,
**no `sorryAx`**.

The resulting unconditional certificate is

```text
D_dup ≤ Σ_(0≤j<i<n) Σ_(p∈P_ij)
          min(2^projectedFree(p.1),2^projectedFree(p.2)),
```

where P_ij contains precisely the actual distinct loss-owner pairs
whose translated blocks intersect. Every contributing pair is
independently shown to have a REAL retained edge whose colour is
one of i,j. The pair carrier is not automatically an empty word or
an unreserved surplus credit.

## Additional legacy compilation repair

`OneSupportGlobalBound.lean` was repaired by moving the `lam` binder
before both `AngleCap p lam` hypotheses. This resolves the Lean
`lam` versus `lam✝` mismatch in
`exists_oneSupportIntervalCertificate`.

Focused CI **38755694671: SUCCESS**, 3,446 jobs.
`oneSupport_centres_dyadic_sum_le_two_pow` uses only
`[propext, Classical.choice, Quot.sound]`, not `sorryAx`.

## New conditional six-source interface

File `ResidualTerminalTwinActualEdgeDyadicSufficient.lean`
contains theorem
`terminalTwinSixSourcePayment_of_actualEdge_dyadic_pairBudget`.
It assumes an external-hole/unreserved-surplus payment of the
original other five debts, actually covered loss-blocker words,
and the conservative dyadic duplicate budget. Under that
hypothesis, the original terminal six-source inequality follows
using the certified exact-retained-edge frontier.

Focused CI **38757291830: SUCCESS**, 3,398 build jobs;
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]`,
with **no `sorryAx`**. Its PAYMENT HYPOTHESIS remains the
unsolved mathematical requirement.

A distinct EXACT, non-conservative IFF theorem is also certified in
`ResidualTerminalTwinExactFirstOccurrenceFrontier.lean`:

- `terminalTwinSixSourcePayment_iff_actualEdge_firstOccurrenceFrontier`
- Focused CI **38757971149: SUCCESS**, 3,397 build jobs;
  axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

This is a literal two-way equivalence of the original terminal
payment and existence of an active flip choice paying the
actual retained-edge covered words, other five debts, and the
**exact first-occurrence** duplicate ledger. The dyadic sufficient
certificate is computationally explicit but may overestimate; the
exact IFF keeps the truly necessary amount without inflation.

## Honest global frontier

Still needed is a planarly valid choice of retained-active loss flips
and a globally non-reusing payment of

```text
terminalTwinOtherFiveDebt
 + |actual chosen-colour retained-edge covered blocker union|
 + D_dup
≤ |outside true holes| + |genuinely unreserved surplus|.
```

The dyadic upper bound on D_dup allows a more explicit, stronger
SUFFICIENT hypothesis in which D_dup is replaced by the certified
pairwise actual-edge cost. This is NOT a new outside-hole supply.
The exact first-occurrence identity may offer a tighter allocation
than the conservative pairwise budget if additional geometry is found.

No full-workspace green build, original theorem proof, or re-submission
eligibility follows solely from these focused certificates.
