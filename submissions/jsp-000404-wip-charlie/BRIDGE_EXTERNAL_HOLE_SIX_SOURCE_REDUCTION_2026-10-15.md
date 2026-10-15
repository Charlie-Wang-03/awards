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

## Continuation 2026-10-15 — active choice, opposite-bit blockers and exact carriers

The following incremental additions are **already kernel-checked** and
independently pass focused GitHub Actions, without `sorryAx` in the new
statements:

- `PlanarLowerBranchActiveExternalHoleFrontier.lean`,
  `planar_lower_branch_capacity_of_exists_active_external_loss_payment`:
  PASS **38725332989**. The conditional planar proof now accepts an
  **existential retained-active flip assignment** satisfying the exact
  external true-hole budget. This is an equivalent *interface* for the
  outstanding terminal six-source payment, not a derivation of the payment.
- `ResidualLossCoveredOppositeBitBlocker.lean`:
  PASS **38725475263**. Every globally covered translated-loss word
  for a genuinely retained-active flip has a different covering vertex
  and both endpoints have opposite canonical bits at a shared
  retained-active coordinate. No global payment injection follows.
- `BadPhasePositiveExponent.lean`: PASS **38725168302**;
  explicit summands repaired in the minimum positive bad-phase proof.
- `OverweightDeletionInduction.lean`: PASS **38725718045**;
  strict-subset induction now uses reverse inclusion correctly.
- `GeneralProjectiveGapDeletion.lean`: PASS **38726187095**;
  noncomputable normalized real gap definitions and `getLast?`
  successor-list recursion repaired.

The admitted root `PlanarLowerBranchProofAdmittedWIP.lean` now calls the
new active-choice conditional theorem. Its statement retains all original
geometric hypotheses and it still has **exactly one executable sorry**.
Its new focused workflow **38725969587** was still in progress at this
documentation update; success is not inferred from the pushed code.

Two more precise carrier constructions are **submitted but not yet certified
at this documentation update**:

1. `ResidualLossCoveredPairBudget.lean`: the set of genuine covered
   translated-loss words is included in a finite union of
   source/blocker/retained-coordinate intersections. Every carrier pair
   is distinct and has opposite bits at a shared active coordinate;
   the resulting word-count upper bound uses `card_biUnion_le`.
   Focused CI **38726615158**, pending.
2. `ResidualLossCoveredExactTripleLedger.lean`: refine those triples
   to carry the source's **actually chosen** active coordinate, then
   establish an **exact set equality** between the covered-loss word set
   and the union of the corresponding source/blocker completion
   intersections. No disjointness across triples is asserted.
   Focused CI **38726911804**, pending.

The independent sorry-free `VerifiedOverlapRewire.lean` imports the
active-choice planar reduction and opposite-bit blocker module. Its
focused CI **38726331856** was running at this update.

**Mathematical blocker remains:** the residual external-hole payment
is not proved. In particular, there is no globally non-reusing
assignment of other terminal debts, opposite-bit covered blockers and
cross-coordinate duplicate mass to outside-translated TRUE holes and
actually unreserved dyadic surplus. All conditional reductions and
exact-cover identities must remain distinguished from a proof of
that missing inequality.

## Follow-on verification and exact blocker-carrier interfaces

- The active-choice WIP root compilation **38725969587: PASS** with its
  explicitly audited single remaining `sorry`. The conditional active-choice
  planar theorem itself passed separately as recorded above.
- The independent **sorry-free** `VerifiedOverlapRewire.lean` root,
  importing both active-choice planar and opposite-bit blocker modules,
  passed **38726331856: SUCCESS**.
- The actual source/blocker/coordinate carrier-set **inclusion** and
  cardinality bound `ResidualLossCoveredPairBudget.lean` passed focused
  CI **38727268633: SUCCESS**. Carrier intersections may overlap.
- `ResidualLossCoveredExactTripleLedger.lean` refines the carrier family
  to exactly the **selected active coordinate** and proposes an **equality**
  with the covered-loss Boolean set. The first CI encountered a nested
  pattern syntax issue; it was repaired and focused CI
  **38727782973: SUCCESS** confirmed the exact set equality.
- Two subsequent conditional reductions were submitted:
  `ResidualTerminalTwinExactBlockerCarrierFrontier.lean` rewrites the
  six-source payment exactly in terms of the chosen-carrier union; and
  `PlanarLowerBranchExactCarrierFrontier.lean` propagates that obligation
  back to the planar lower-branch theorem. Their focused CIs are pending
  (**38727817652**, **38727968899**). Neither is certified until PASS.

In all cases, the global injective allocation of genuine exterior holes and
unreserved surplus against the five/six non-loss debt terms, actual covered
blocker carriers and duplicate debt remains unproved. New equivalences
must not be confused with the truth of the shared payment inequality.

## Continuation — exact source/blocker retained-edge restriction and local capacities

This section records facts verified later than the historical in-progress
snapshots above; those old snapshots should not be read as current CI status.

### Kernel-checked actual results

- `ResidualTerminalTwinExactBlockerCarrierFrontier.lean` CI
  **38727817652 SUCCESS**, `PlanarLowerBranchExactCarrierFrontier.lean`
  CI **38728586815 SUCCESS**, and the sorry-free
  `VerifiedOverlapRewire.lean` root CI **38728671044 SUCCESS**.
  The main WIP was subsequently refactored to invoke the exact-carrier
  planar theorem with its ONE original unproved six-source payment.
  Its dedicated compilation CI **38731956179 SUCCESS**. This is a
  compiles-with-one-sorry claim, not a completed proof.
- `ResidualLossBlockerTripleLocalCapacity.lean` independently passed
  **38732065805 SUCCESS**: each source/blocker/coordinate intersection
  has cardinality at most
  `min (2 ^ projectedFree(source)) (2 ^ projectedFree(blocker))`.
  It also proves the corresponding upper bound summed over genuinely
  chosen opposite-bit carrier triples. The sum may overcount overlapping
  intersections; it is an upper bound, not a hole allocation.
- `ResidualLossBlockerEdgeColourRigidity.lean` independently passed
  **38732522439 SUCCESS**: if a projected-loss source `v` has its
  completion word flipped at retained coordinate `c` and the result
  belongs to the completion cube of a different blocker `w`, then
  the ACTUAL source--blocker edge is retained with EXACT colour `c`,
  whichever of `v<w` or `w<v` holds.
  The proof uses the loss owner's residual inactivity and the
  canonical opposite retained edge bits. It makes no claim that such
  same-colour neighbours are unique.
- Legacy independent Lean repairs: `ZeroClusterAngle.lean` CI
  **38732265521 SUCCESS** (real-positive radial parameters) and
  `TopExponentMultiplicity.lean` CI **38732834714 SUCCESS** (correct
  AngleCap parameter binder and tailCount module import).

### Pending integration and remaining mathematical work

`ResidualLossActualEdgeCarrierFrontier.lean` (focused CI
**38733102250 SUCCESS**) strengthens the exact selected carrier union:
the only contributing triples must be **actual same-colour retained
source/blocker edges**, not merely opposite-bit shared-active candidate
pairs. An actual-edge-restricted local dyadic sum bound is also certified.

Corresponding exact terminal and planar conditional fronts are committed
in `ResidualTerminalTwinActualEdgeCarrierFrontier.lean` and
`PlanarLowerBranchActualEdgeCarrierFrontier.lean`. Their CI runs
**38733253482** and **38733316709** were pending at this update;
do not count these theorems as independently certified until those
checkers finish successfully.

`AggregateSplitHardStopResolution.lean` repaired the formerly malformed
set-complement definition and a missing numerical normalization. Its
focused check **38733732063** was pending.

IMPORTANT: `OrderedEdgeColoring.noMonoTwoPath` forbids same-colour
increasing two-step paths; it is NOT a proper edge-colouring axiom that
would make all incident edge colours distinct. Consequently the
same-colour retained neighbour of a loss vertex need **not** be unique,
and no such uniqueness shortcut is used.

The remaining unproved inequality is the globally non-reusing
payment of all other terminal debt, these actual retained-edge
covered-loss carriers and cross-coordinate loss duplicate debt from
TRUE holes outside the translated loss union plus genuinely unreserved
dyadic surplus. No Lean patch has eliminated that obligation.

## Continuation — actual-colour frontier successfully certified in Lean

Subsequent focused CI outcomes supersede the in-progress status of the
preceding section:

- `ResidualTerminalTwinActualEdgeCarrierFrontier.lean`: focused
  GitHub Actions **38733253482 SUCCESS**. The ORIGINAL terminal
  six-source payment is **logically equivalent** to an existential
  retained-active choice whose covered-loss payment term is the EXACT
  Boolean union indexed only by ACTUAL retained source--blocker edges
  with colour equal to the selected flip coordinate. The old loss
  completion mass is handled by the already proven true-hole and
  duplicate-debt ledger, without double-counting hole credits.
- `PlanarLowerBranchActualEdgeCarrierFrontier.lean`: focused
  GitHub Actions **38733316709 SUCCESS**. Under the ORIGINAL AngleCap
  and normalized lower-branch assumptions, the actual-edge payment
  condition is sufficient to prove the lower-branch dyadic bound.
  The terminal payment condition is NOT proved by this theorem.
- `AggregateSplitHardStopResolution.lean`: repaired the malformed
  complement operation and an unnormalized power bound; focused
  GitHub Actions **38733992552 SUCCESS**. This is an arithmetic
  regression theorem, not a geometric proof of a universal split.

The WIP main source has now been changed to invoke
`planar_lower_branch_capacity_of_actual_retainedEdge_payment` and
keeps EXACTLY ONE executable `sorry`. The sorry-free independent
`VerifiedOverlapRewire.lean` umbrella imports the verified actual-edge
frontier. Their latest focused CI runs **38734056676** and
**38734097309** were still in progress when this paragraph was added;
successful antecedent theorem checks must not be conflated with
unverified root re-compilation.

An optional stronger numerical certificate
`ResidualTerminalActualEdgeDyadicSufficient.lean` bounds each
actual-edge blocker intersection by the minimum of its two endpoint
projected dyadic capacities. Its hypothesis replaces the cardinality
of the exact carrier UNION with a SUM of local endpoint minima.
The resulting hypothesis is STRICTLY SUFFICIENT, **not equivalent**,
because different source--blocker edges may carry intersecting
Boolean word sets. Focused CI **38734311244** was pending.

**Open mathematical obstruction remains unchanged in truth value:**
the genuine outside-translation Boolean holes and genuinely unreserved
dyadic surplus must globally pay the remaining soft, net hard, twin and
mixed-rigid obligations, PLUS the exact actual-edge covered-loss UNION
and cross-coordinate translated-loss duplicate debt. No global
non-reusing payment or disproving counterexample is established.
