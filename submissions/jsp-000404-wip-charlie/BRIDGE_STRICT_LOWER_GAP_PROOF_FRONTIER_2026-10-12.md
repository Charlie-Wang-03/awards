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


## New certified lower-shell decomposition and local dyadic ledger

Date: 2026-10-12. Work continues only in
`research/jsp-000404-sharp-centre`; this is research, NOT an upstream
proof claim.

**Certified sources newly added:**
- `JSP000404Research/ResidualStrictUnusedLowerSinkClassification.lean`
  (2 theorems).
- `JSP000404Research/ResidualStrictRigidLowerShellDecomposition.lean`
  (9 theorems, including 4 direct dyadic local-capacity results).
Both are imported from the sorry-free independent umbrella
`JSP000404Research/VerifiedOverlapRewire.lean`.

Write `S` for `netStrictDescentRigidCarriers C exponent`, `Q_v`
for `retainedCompletionWords C v`, `R` for
`netStrictDescentRigidWords C exponent`, `L` for
`netStrictRigidLowerCapacityWords C exponent`, and `U=L \ R`.

**First new theorem family: stronger classification of U.**
Every word in U has its uniquely determined strict-rigid LOWER origin.
If that word also belonged to ANY hard-overlap face, unique residual
lower completion ownership and the global hard-carrier vertex matching
would identify that hard carrier with its strict-rigid source.
The word would then lie in R, contradiction. Thus

```text
U INTER hardOverlapCompletionWords = EMPTY
U SUBSET singletonCompletionWords UNION softOverlapCompletionWords
U SUBSET coveredCompletionWords
U INTER trueBooleanHoles = EMPTY
```

These assertions are unconditional in the ordered-colouring setting;
no fake global Hall assumption or genuine-planar payment is used.

**Second new theorem family: exact LOCAL strict shell decomposition.**

```text
U = DISJOINT_UNION_(q in S) (Q_(q.lower) \ Q_(q.upper))
card(U) = SUM_(q in S) card(Q_(q.lower) \ Q_(q.upper))
```

For a strict rigid q, the upper completion cube is contained in its
lower cube (the already certified no-outgoing rigid property).
Under the verified one-layer endpoint saturation, EACH local shell has
the exact target-dyadic size

```text
card(Q_(q.lower) \ Q_(q.upper))
  = 2 ^ exponent(q.lower) - 2 ^ exponent(q.upper)
```

so, with no cross-carrier duplicate counting,

```text
card(U) = SUM_(q in S)
   (2 ^ exponent(q.lower) - 2 ^ exponent(q.upper))

card(forwardReverseBridgeSoftWords C exponent)
  <= SUM_(q in S)
   (2 ^ exponent(q.lower) - 2 ^ exponent(q.upper))
```

Each individual shell is itself a subset of singleton-or-soft COVERED
words. The mass difference is real and locally allocated, but still
CANNOT be paid as true Boolean holes or newly available profile surplus.

**Lean regression and real compiler fixes:**
- https://github.com/Charlie-Wang-03/awards/actions/runs/38227675869
  first run failed at a definitional mismatch
  (`carrierOverlapWords` versus its explicit two-cube intersection).
- Fix `ba692b11ceea86856b3c49bf4dfc0faa9b330fcc` added explicit
  `change`. PASS:
  https://github.com/Charlie-Wang-03/awards/actions/runs/38228132727 .
- Shell decomposition before per-carrier weights: PASS,
  https://github.com/Charlie-Wang-03/awards/actions/runs/38228462391 ,
  3,477 build jobs.
- https://github.com/Charlie-Wang-03/awards/actions/runs/38228896550
  failed only because the `projectedFree` abbreviation was not
  unfolded in the local cube-cardinality proof.
- Fix `0e525ff910140b37eeefe4cc9cd04ee2ba7cef69` explicitly
  normalizes `projectedFree`. PASS:
  https://github.com/Charlie-Wang-03/awards/actions/runs/38229121810 ,
  3,217 build jobs.
- All 11 new theorem axiom prints are exactly
  `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.
- The targeted hole scanner continues to report EXACTLY ONE allowed
  executable `sorry` in
  `JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean:132`.
  The WIP module is excluded from the independent green umbrella.

**Unclosed mathematical obligation is unchanged in number.**
The remaining six-source global payment compares soft overlap,
forward and reverse movable hard faces, equal-exponent twins, both
mixed-rigid target debts, and projected profile loss against genuine
Boolean holes and genuinely unreserved surplus. Nothing in this
local lower-shell partition proves that global geometric allocation.

The new results isolate a finite family of strictly local, non-reused
shells as precise geometric objects for the NEXT attempted payment
argument. They are not a completed JSP-000404 proof, and no upper
branch or original theorem is declared solved.


## Oriented strict-shell outgoing-soft ledger (2026-10-12)

This research increment is a **valid structural reduction, not an award
solution**. The entire true-hole plus genuinely-unreserved-surplus
six-source payment inequality remains open and explicitly admitted in
`PlanarLowerBranchProofAdmittedWIP.lean`. A single `sorry` there is
not evidence that the missing mathematics is small.

### A. Oriented ownership, no new assumptions

Module:
`JSP000404Research/ResidualStrictShellSoftOwnerOrientation.lean`.

Let `q=(a,v)` be a strict-descending terminal rigid carrier, and
`w in Q_a \ Q_v` be a SOFT overlap word. If `w` belongs to the
soft residual carrier `r=(b,z)`, then:

```text
b = a
z != v
a < z  (because r is an ordered residual carrier)
```

The crucial equality follows from **residual lower-cube word
uniqueness**: `w` lies in the lower cubes of both residual carriers.
The upper endpoints differ because one carrier is HARD and the other
SOFT. There are four new independent Lean theorems, all without
`sorryAx`.

CI PASS:
https://github.com/Charlie-Wang-03/awards/actions/runs/38237647007
(3,478 successful jobs).

### B. Full outgoing SOFT faces and an exact per-carrier identity

Module:
`JSP000404Research/ResidualStrictShellSoftMassLedger.lean`.

For a SOFT carrier `r=(a,z)` outgoing from the strict carrier
`q=(a,v)`, the **entire** overlap face `Q_a intersect Q_z` is
contained in the lower shell `Q_a \ Q_v`: the upper cubes `Q_z`
and `Q_v` are disjoint, as both are upper endpoints of distinct
residual edges.

Conversely, every SOFT word in the shell has just such an owner.
The overlap faces are pairwise disjoint by the earlier exact
residual-carrier word ownership theorem.

Writing `SoftOut(a)` for all nonempty SOFT overlap carriers whose
lower endpoint equals `a`, the following holds as an exact
finite-cardinality equality under the verified one-layer budget:

```text
2^k(a) - 2^k(v)
  = card((Q_a \ Q_v) intersect singletonCompletionWords)
    + SUM_(r in SoftOut(a)) 2^card(commonRetainedInactive(r)).
```

There are five new independent Lean theorems, including the full
set-level equality, disjoint dyadic mass sum, and the local equality.

A first run exposed two **Lean script** defects, not mathematical
counterexamples: a missing existential carrier witness and a
`rw` that rewrote local binder occurrences. These were repaired
by explicitly supplying `r` to `Finset.mem_biUnion` and replacing
the problematic rewrite with a directed `calc` chain.

Initial failing CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38238146947

Corrected CI PASS:
https://github.com/Charlie-Wang-03/awards/actions/runs/38238465805
(3,479 successful jobs, zero `sorryAx` in all five new theorems).

### C. Genuine planar specialization

Module:
`JSP000404Research/PlanarStrictShellSoftMassLedger.lean`.

One new Lean theorem specializes the exact local mass ledger to
the genuine `AngleCap` geometry, actual standard residual
colouring, and the true centre-projective-cycle target exponents.
The required `hexp` and `honeLoss` hypotheses are **derived**
from established planar estimates; they are not assumed independently.

Planar CI PASS:
https://github.com/Charlie-Wang-03/awards/actions/runs/38238758562
(3,480 successful jobs, no `sorryAx` for the new planar theorem).

The theorem is also referenced as `hlocalShellMass` at the
research-only admitted final-payment WIP boundary. The WIP itself
retains its single `sorry`; adding this derived input does NOT
assert or discharge the missing global inequality.

### D. Mathematical limit and next obstruction

The ledger is more precise than the global dyadic descent-gap bound:
it identifies **every soft face** inside the shell and distinguishes
it from genuinely singly covered words without multiple charges.
But EVERY term above counts ALREADY-COVERED Boolean words. Neither
these words nor the strict dimensional descent gap can simply be
booked as a **true Boolean hole** or a **net unreserved dyadic profile
surplus**.

The missing result must couple this local covered-word accounting
to external genuine holes/unused profile surplus in the actual
planar configuration, while nonredundantly accounting for the
remaining TWIN and both mixed-rigid target debts and profile loss.

No final lower-branch capacity bound, full JSP-000404 theorem,
counterexample or upstream-ready claim is established by this work.


WIP integration regression **PASS**:
https://github.com/Charlie-Wang-03/awards/actions/runs/38239149059
(3,402 build jobs). The hole scanner finds **exactly one**
intentional executable `sorry` at
`PlanarLowerBranchProofAdmittedWIP.lean:140`, and
`#print axioms planar_lower_branch_dyadic_capacity_admitted_wip`
honestly reports `sorryAx`. All newly proved standalone
structural and planar theorems have no `sorryAx`.


## Global singleton / bridge / nonbridge shell reserves

**Research branch:** `research/jsp-000404-sharp-centre`.
This increment proves a globally disjoint covered-word conservation
ledger and specializes it to the genuine planar `AngleCap` objects.
It does **not** close the original lower-branch conjecture.

### Certified abstract theorem family

Module: `JSP000404Research/ResidualStrictShellGlobalReserveLedger.lean`.
Twelve new abstract theorems were established across this increment:
eight in the initial module and three further explicit three-way
reservation lemmas, plus one actual-planar specialization described
below (11 abstract + 1 planar total).

Let `S` be the strict-descent terminal rigid carriers,
`U` their disjoint lower-minus-upper completion shells, and
`B` the potential forward/reverse bridge-soft word pool.
Define literal, globally disjoint, finite sets:

- `A = U ∩ singletonCompletionWords`;
- `T = U ∩ softOverlapCompletionWords`;
- `N = T \ B` (soft words which cannot be candidate bridge collisions).

The new Lean theorems certify:

```text
U = A DISJOINT_UNION T
B SUBSET T
T = B DISJOINT_UNION N

card(U) = card(A) + card(B) + card(N)

card(U) =
  SUM_(q in S) (2^exponent(q.lower) - 2^exponent(q.upper))

THEREFORE
card(A) + card(B) + card(N) =
  SUM_(q in S) (2^exponent(q.lower) - 2^exponent(q.upper))

and in particular
card(B) + card(A) <= SUM_strict_local_dyadic_gaps.
```

This refines the earlier inequality for potential bridge collisions:
singleton-covered words are **provably unavailable** as collision
slots. In fact, the entire nonbridge-soft portion `N` can also be
removed by exact equality, without reusing a Boolean word.

The global soft part `T` has an additional exact dyadic identity:

```text
card(T) =
  SUM_(q in S)
    SUM_(r in outgoingSoftCarriers(q.lower))
      2^card(commonRetainedInactive(r)).
```

This is not a claim that the counted words are holes: all
of `A`, `B` and `N` are **ALREADY COVERED** words.

### Genuine planar theorem

Module: `JSP000404Research/PlanarStrictShellReserveLedger.lean`.

`planar_strict_shell_singleton_bridge_nonbridge_exact_ledger`
proves the entire three-way exact equality for the *actual*
standard residual colouring of injective plane points under
`AngleCap p lam`, `t=n+delta`, `0<=delta<1/2`, and the
centre-projective-cycle exponent function.

There is no new assumed one-layer input: the proof derives
the exponent and active-colour budget from the established planar
results. All new lemmas were imported into the independent
sorry-free umbrella `VerifiedOverlapRewire.lean` and had only
`[propext, Classical.choice, Quot.sound]` in their `#print axioms`
outputs—zero `sorryAx`.

### Verified GitHub Actions and WIP

- Initial global 8 theorem module: [CI #38248662920](https://github.com/Charlie-Wang-03/awards/actions/runs/38248662920) — **PASS, 3,481 jobs**.
- Added exact nonbridge-soft remainder and three-way ledger:
  [CI #38249056356](https://github.com/Charlie-Wang-03/awards/actions/runs/38249056356) — **PASS, 3,220 jobs**.
- Genuine planar `AngleCap` specialization:
  [CI #38249341201](https://github.com/Charlie-Wang-03/awards/actions/runs/38249341201) — **PASS, 3,482 jobs**.
- Integrated `hglobalShellReserve` into the sole admitted WIP:
  [CI #38249753124](https://github.com/Charlie-Wang-03/awards/actions/runs/38249753124) — **PASS, 3,404 jobs**.

The WIP scanner and independent axiom report continue to agree:
**one** intentional executable `sorry` remains, now at
`JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean:148`.
Its final statement still depends on `sorryAx`, whereas all new
standalone theorems do not. No new unresolved Lean compilation
errors remain after this increment.

### Precise remaining mathematical frontier

The strict-rigid shell's previously unused covered-word pool is
now partitioned exactly and globally without double counting.
Nevertheless, the final SIX-SOURCE defect payment still has to
relate **actual Boolean holes plus genuinely unreserved profile
surplus** to total soft overlap, forward/reverse mobile hard, rigid
twin and mixed-rigid target debts, and projected-profile loss.

Nothing in the newly certified shell ledger turns covered words into
true holes, or gives an independent source of unreserved surplus.
The only `sorry` is genuinely mathematical, not a Lean syntax
error. The original JSP-000404 problem remains **unproved and
undisproved** by this downstream branch.
