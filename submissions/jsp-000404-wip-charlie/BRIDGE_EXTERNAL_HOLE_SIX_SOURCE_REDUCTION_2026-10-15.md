# JSP-000404 — Exact external-hole reduction of the sole six-source sorry
Date: 2026-10-15
Branch: `research/jsp-000404-sharp-centre`

## Fully verified steps

1. `ResidualLossTrueHoleCoverPartition.lean`: the original
   `totalDyadicProfileLoss` is the sum of translated target words that are
   **true global Boolean holes**, translated target words still **covered**,
   and **cross-coordinate duplicate-overcount debt**.
   GitHub Actions **38718940944 PASS**; no `sorryAx`.
2. `ResidualLossExternalHoleBudget.lean`: the hole total splits into those
   hit by the translated loss union and those **outside** that union. By
   cancelling the same legitimate hit-hole cardinality from the payment
   inequality, one gets the **exact iff**:
   ```text
   otherDebt + profileLoss <= allTrueHoles + availableSurplus
       iff
   otherDebt + coveredTranslated + duplicateDebt
       <= outsideTranslatedTrueHoles + availableSurplus.
   ```
   GitHub Actions **38719398322 PASS**; no `sorryAx`.
3. `ResidualTerminalTwinExternalHoleFrontier.lean` instantiates this
   equivalence with every **actual** terminal-twin six-source quantity,
   including both net mobile hard masses, terminal equal-exponent twins,
   ascending and descending mixed-rigid masses, soft overlap, and all
   existing explicitly reserved-surplus deductions. Global hole count
   is proved equal to `2^n - |coveredCompletionWords|`.
   GitHub Actions **38719664242 PASS**; no `sorryAx`.
4. `PlanarLowerBranchExternalHoleFrontier.lean` uses the established
   AngleCap-to-standard-residual bridge and the exact iff to establish a
   **conditional planar capacity theorem** from the external-hole payment.
   GitHub Actions **38720866891 PASS**; no `sorryAx`.
5. `LocalPaletteCertificate.lean` old elaboration failures fixed,
   GitHub Actions **38719126304 PASS**.
6. `AlternativeKraftExtremizer.lean` old five-leaf Kraft arithmetic
   and list-filter proof fixed, GitHub Actions **38719848383 PASS**.

## Explicit current admitted boundary

`PlanarLowerBranchProofAdmittedWIP.lean` now invokes
`planar_lower_branch_capacity_of_external_loss_obstruction` instead of
`planar_lower_branch_dyadic_capacity_of_terminal_twin_net_payment`.
Its **one and only** executable `sorry` is left in the new equivalent
external-hole condition. The main theorem statement, AngleCap assumptions,
and all prior verified statements remain unchanged.

The independent WIP compilation workflow
`JSP-000404 Focused Admitted External Hole Lean` was started. Its result
MUST be checked; no kernel success is inferred from simply pushing a file.

## Further genuinely active flips (verification pending)

`ResidualLossActiveFlipBlocker.lean` proves intended theorems that each
projected-loss owner admits an actually retained-active flip choice under
`k(v)<=n`, and every globally covered translated word of such a choice
has a **different** covering owner, with that flip coordinate active at
both vertices.

`ResidualTerminalTwinActiveExternalFrontier.lean` proposes the more
natural exact iff: six-source payment iff there exists a globally
retained-active flip choice satisfying the external-hole budget.
Its independent CI is in progress and no success is claimed here.

## What has NOT been proved

- No global injection or non-reusing allocation of the remaining covered
  translated words, duplicate debt, and soft/forward/reverse/twin/mixed
  obstructions into the outside true holes plus genuinely unreserved surplus.
- An equivalence is not a proof that its right-hand inequality holds.
- True holes already used by another debt cannot be used again.
- The sole admitted `sorry` is NOT eliminated. Original JSP-000404
  is neither fully proved nor disproved.
- Full Fast Incremental Lean CI is NOT green: unrelated legacy Lean modules
  still have errors. Focused CI success must not be conflated with complete
  project compilation or final theorem correctness.
