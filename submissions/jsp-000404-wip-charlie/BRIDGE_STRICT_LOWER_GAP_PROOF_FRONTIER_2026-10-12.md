# JSP-000404: bridge-soft versus strict-rigid shared lower-cube capacity

Date: 2026-10-12. Research branch: `research/jsp-000404-sharp-centre`.

## Boundary and status

**No full JSP-000404 proof or disproof.** The research-only
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean` still has
**one executable `sorry`**, explicitly reported as `sorryAx`.
The independent `VerifiedOverlapRewire.lean` does not import WIP.

Previous verified results established:
- A globally injective FORWARD map of outgoing transportable hard
  overlap faces into already-covered singleton/soft Boolean words.
- A globally injective REVERSE map of strict-descending terminal rigid
  hard overlap faces into already-covered singleton/soft words.
- Every actual cross-map collision has a unique oriented SOFT bridge
  carrier `(reverseRigid.lower, forwardHard.upper)`.
- The potential bridge soft collision pool `Bridge` has an EXACT
  power-of-two face decomposition
  `|Bridge| = SUM_(e in bridgeSoftCarriers) 2^|commonInactive(e)|`.
- Global cross-map mass capacity
  `forwardHardMass + reverseHardMass
     <= singletonCoveredMass + softCoveredMass + bridgeSoftMass`.
  These COVERED words are not TRUE Boolean holes.

## New result 1: both bridge-soft and reverse strict hard mass share LOWER cubes

New Lean module:
`JSP000404Research/ResidualBridgeReverseLowerSharedCapacity.lean`.

Let `Q_b := retainedCompletionWords C b`,
`S := netStrictDescentRigidCarriers C exponent`,
`R := netStrictDescentRigidWords C exponent`, and let
`B := forwardReverseBridgeSoftWords C exponent`.

For every soft bridge carrier `(b,v)`, its defining provenance
contains a strict terminal rigid carrier `(b,z) in S`. Thus its
ENTIRE potential bridge face is contained in `Q_b`.

Every reverse strict-rigid hard source word also belongs to `Q_b`
of its original rigid carrier.

Furthermore `B\cap R=empty`: bridge words have SOFT ordered overlap
owners; strict source words have HARD owners; these classes were
previously proved word-disjoint. Consequently,

```text
B UNION R SUBSET UNION_((b,z) in S) Q_b
|B| + |R| <= |UNION_((b,z) in S) Q_b|.
```

This is a SHARED finite capacity, NOT two independent sink budgets.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38214846843
(3,212/3,212 PASS; four theorem axiom audits without `sorryAx`).

## New result 2: the lower cubes are disjoint, with exact dyadic mass

New module:
`JSP000404Research/ResidualBridgeReverseLowerDyadicBudget.lean`.

Distinct strict-rigid hard carriers form a vertex matching. If the
two LOWER completion cubes of two different carriers had a common
Boolean word, `residual_lower_completion_word_unique` would
identify their lower endpoints, forcing the carriers equal by the
hard vertex matching theorem. Therefore their full lower cubes
are pairwise disjoint:

```text
|UNION_((b,z) in S) Q_b|
  = SUM_((b,z) in S) |Q_b|
  = SUM_((b,z) in S) 2^projectedFree(b).
```

Under the certified one-layer active profile budget
`activeCard(i) <= n - exponent(i) + 1`, every surviving rigid
hard carrier is DOUBLE SATURATED, hence
`projectedFree(b)=exponent(b)`. Therefore:

```text
|B| + |R| <= SUM_((b,z) in S) 2^exponent(b).
```

First CI hit only a Lean representation mismatch: a
`Set.PairwiseDisjoint` proof goal was expressed as
`Function.onFun Disjoint`; inserting `change Disjoint (Q_p) (Q_q)`
before `Finset.disjoint_left` fixed it.
Fix commit `64dc5bb3fe0bab852538634c8bbeb9b2cbca1d69`.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38215280186
(3,213/3,213 PASS; five theorem axiom audits without `sorryAx`).

## New result 3: precise STRICT target-weight descent gap

New module:
`JSP000404Research/ResidualBridgeStrictDyadicDescentGap.lean`.

The entire reverse strict-rigid hard source family consists of
disjoint whole hard faces, each doubly saturated and of exact
UPPER target weight. Certified equation:

```text
|R| = SUM_((b,z) in S) 2^exponent(z).
```

Subtracting this from the shared lower-cube capacity in NATURAL
finite cardinal arithmetic establishes the quantitative bound:

```text
SUM_(e in bridgeSoftCarriers) 2^|commonInactive(e)|
  = |B|
  <= (SUM_((b,z) in S) 2^exponent(b))
       - (SUM_((b,z) in S) 2^exponent(z)).
```

This is the **STRICT DIMENSION DESCENT gap** available *inside*
lower completion cubes, not a profile surplus. In fact the two
rigid endpoints have ZERO dyadicProfileSurplus. The theorem does
not justify moving the gap to the original true-hole/surplus side
of the admitted global payment without a fresh allocation argument.

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38215573532
(3,214/3,214 PASS; three axiom audits without `sorryAx`).

## New result 4: genuine planar AngleCap specialization

New module:
`JSP000404Research/PlanarBridgeSoftStrictDyadicGap.lean`.

For an actual injective planar configuration satisfying
`AngleCap p (pi/t)`, `t=n+delta` with `0<=delta<1/2`,
and the family of `CentreProjectiveCycle` witnesses, define
the genuine standard residual colouring `B` and exponent
`k(i)=centreExponent(cycle_i,t)`.

The existing planar one-layer active-card theorem derives the
hypotheses of the abstract gap, giving the SAME bound as above
with the genuine planar data and `k`:

```text
SUM_(bridgeSoft e of B,k) 2^|commonInactive_B(e)|
 <= SUM_(strictRigid q of B,k) 2^k(q.lower)
     - SUM_(strictRigid q of B,k) 2^k(q.upper).
```

This is NOT an arbitrary DirectionData/Hall postulate.
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38215809320
(3,394/3,394 PASS; planar theorem axioms are
`propext`, `Classical.choice`, `Quot.sound` only).

## WIP reduction and remaining mathematical obstacle

In `PlanarLowerBranchProofAdmittedWIP.lean` the previously
certified `hmobile` bound is now accompanied by a genuine planar
`hbridgeGap` theorem for potential cross-map collisions.
There remains precisely ONE admitted `sorry` representing the
six-source true-hole / unreserved-profile-surplus global payment.
WIP run:
https://github.com/Charlie-Wang-03/awards/actions/runs/38216044106
(3,396/3,396 PASS; one intended `sorryAx`).

The remaining goal cannot currently be completed by simply
combining these estimates:
- `singletonCompletionWords` and `softOverlapCompletionWords`
  are already COVERED words, not TRUE holes.
- `SUM_strict(2^k(lower)-2^k(upper))` is a dimensional capacity
  difference INSIDE saturated rigid lower cubes. It is NOT
  an unreserved `dyadicProfileSurplus` and cannot be double charged.
- The exact equal-target twin rigid debts, previously credited
  mixed-rigid targets, soft overlaps, and projected profile losses
  must all be paid non-redundantly in the final inequality.
- New genuinely planar coupling or another global injection/payment
  invariant is required to bridge these bookkeeping objects.

The four sorry-free files are imported by
`JSP000404Research/VerifiedOverlapRewire.lean`, which excludes WIP.
Full CI run:
https://github.com/Charlie-Wang-03/awards/actions/runs/38216270221 .

Do not claim a solved lower branch, complete JSP-000404, or an
unconditional Hall expansion from this handoff.


## Word-level unused lower-cube partition and no-hole audit

New certified Lean module:
`JSP000404Research/ResidualBridgeStrictUnusedLowerCapacity.lean`.

Let `L = netStrictRigidLowerCapacityWords C k`,
`R = netStrictDescentRigidWords C k`, and
`B = forwardReverseBridgeSoftWords C k`.
Define `U = L \\ R` as **unused lower-cube slots**, NOT global
Boolean holes. The kernel-certified chain now proves:

```text
B SUBSET U                                    (word-level)
card(B) <= card(U)
card(U) = SUM_strict 2^k(lower) - SUM_strict 2^k(upper)
U SUBSET coveredCompletionWords C
U INTER (univ \\ coveredCompletionWords C) = EMPTY
```

The last two statements are significant for adversarial correctness:
even the unused strict-rigid LOWER-cube slots are covered by at least
one original retained completion cube, so **not one** of these slots
can be directly charged as a TRUE Boolean hole. The strict descent
gap is mathematically real but is NOT the unreserved dyadic profile
surplus. It remains invalid to subtract/credit this gap on the
true-hole side of the still-admitted global-payment inequality.

Five new theorem names (all in `JSP000404Research.OrderedEdgeColoring`):
`bridge_soft_subset_unused_strict_lower_words`,
`bridge_soft_card_le_unused_strict_lower_words`,
`unused_strict_lower_words_card_eq_dyadic_gap`,
`unused_strict_lower_words_subset_covered`, and
`unused_strict_lower_words_disjoint_true_holes`.

Proof regression:
- https://github.com/Charlie-Wang-03/awards/actions/runs/38224203801
  — 3,475 jobs PASS for the first three theorems.
- https://github.com/Charlie-Wang-03/awards/actions/runs/38224550204
  — 3,215 jobs PASS for all five theorems.
- All five printed axiom sets:
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Exactly one intentional executable `sorry` remains in
  `PlanarLowerBranchProofAdmittedWIP.lean:132`; this WIP is still
  deliberately excluded from the sorry-free verification umbrella.
- Targeted CI preflight was tightened from
  `--wip-max-sorries 2` to `--wip-max-sorries 1`.
  Its success does not certify the admitted WIP theorem.

**Remaining mathematical gap unchanged in count:** the one genuine
global six-source TRUE-hole plus UNRESERVED-profile-surplus payment
lemma. The new results sharpen the allowed allocation/obstruction
ledger; they do NOT close that lemma and do NOT solve JSP-000404.
