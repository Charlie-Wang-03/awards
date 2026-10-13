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


## Exact actual-collision frontier restricted to net-unpaid mobile sources

Date: 2026-10-12. Research branch only; **the original JSP-000404 remains
unproved and undisproved**. The result below is an exact accounting
refinement rather than the missing true-hole payment.

### Actual forward/reverse collisions (eight Lean theorems)

The new module *ResidualActualBridgeCollisionLedger.lean* defines
the ACTUAL collision set I as the intersection of the two established
globally injective full-forward and reverse-strict sink images, not
the complete candidate bridge-soft face pool B.

Lean certifies:

~~~text
I SUBSET B
reverse-strict sink image SUBSET strict-rigid lower-minus-upper U
fullForwardSourceMass + reverseStrictSourceMass
  = card(forwardSink UNION reverseSink) + card(I)
  <= singletonCoveredMass + softCoveredMass + card(I)

card(B) = card(I) + card(B \ I).
~~~

The reverse sink image is a concrete occupied subset of U, with its
exact reverse source mass preserved. The potential noncolliding bridge
pool cannot be double-charged as a genuine transport intersection.

A real Lean cardinal-arithmetic error was repaired by providing
the cardinal consequence of the reverse-sink subset inclusion.
**PASS:** https://github.com/Charlie-Wang-03/awards/actions/runs/38252954027
(3,483 jobs; eight theorem axiom prints have no sorryAx).

### Exact unused sink credit (four Lean theorems)

Module: *ResidualActualMobileSinkSlack.lean*.

Singleton-covered words S and soft-overlap words T are disjoint
(completion multiplicities 1 and 2). Define

~~~text
E = (S UNION T) \ (forwardSink UNION reverseSink).

fullForwardSourceMass + reverseStrictSourceMass + card(E)
  = card(S) + card(T) + card(I).

fullForwardSourceMass + reverseStrictSourceMass
  + card(E) + card(B \ I)
  = card(S) + card(T) + card(B).
~~~

The previous coarse candidate-bridge inequality discarded two
separate nonnegative slacks: unused eligible covered sinks E and
candidate bridge words B\I which are never actual collisions.
Neither counts as a genuine Boolean hole.

**PASS:** https://github.com/Charlie-Wang-03/awards/actions/runs/38253346594
(3,484 jobs; zero new sorryAx).

### Restriction to genuinely NET UNPAID forward hard words (eight theorems)

Module: *ResidualNetActualCollisionLedger.lean*.

The previous full-forward sink image may contain hard source words
ALREADY PAID by dyadic profile surplus. The final six-source WIP debt
includes ONLY the net-unpaid forward hard source words. To eliminate
this pollution, the forward map was restricted to the exact
netTransportableHardWords source subtype; Lean checks global
injectivity of that restriction and exact cardinality of its image.

Write F_net for its image, R for the reverse strict-rigid sink image,
I_net for their actual intersection, and E_net for the unused
eligible singleton/soft sink words.

~~~text
I_net = F_net INTER R
I_net SUBSET I SUBSET B
E_net = (S UNION T) \ (F_net UNION R)

netUnpaidForwardMass + reverseStrictSourceMass + card(E_net)
  = card(S) + card(T) + card(I_net).
~~~

A new generic Lean theorem rigorously proves, for EVERY external
otherDebt and availableBudget:

~~~text
(otherDebt + netUnpaidForwardMass + reverseStrictSourceMass
   <= availableBudget)
  IFF
(otherDebt + card(S) + card(T) + card(I_net)
   <= availableBudget + card(E_net)).
~~~

This isolates a sharper equivalent form of the only unpaid
geometric payment: actual collisions, not candidate face mass;
unused eligible covered sinks on the credit side; and no repeated
profile-surplus-paid forward hard sources.

The first restricted-injection Lean run exposed a subtype projection
type mismatch. Fix: type the value projection over the ORIGINAL
transportable-source subtype when transporting source equalities.
No proof hypothesis was changed.

**PASS:**
https://github.com/Charlie-Wang-03/awards/actions/runs/38254298773
(3,485 jobs; seven new net sink theorems),
https://github.com/Charlie-Wang-03/awards/actions/runs/38254627213
(3,223 jobs; one more payment-IFF theorem).
All eight have no sorryAx.

### True planar AngleCap specialization

Module: *PlanarNetActualCollisionPaymentFrontier.lean*.

The verified theorem
*planar_net_unpaid_mobile_payment_iff_actual_sink_credit*
derives the genuine standard-residual one-layer exponent and
active-card budget witnesses from AngleCap and centre projective
cycles and then proves the exact NET mobile payment equivalence
uniformly for all remaining debt and available budget values.

**PASS:** https://github.com/Charlie-Wang-03/awards/actions/runs/38255039291
(3,486 jobs; the new planar theorem has only the standard Lean axioms
propext, Classical.choice, Quot.sound).

### WIP integration and remaining open geometry

The sole admitted WIP entry now includes a certified
*hnetPaymentFrontier* derived from the genuine planar theorem,
alongside the earlier shell and possible-bridge estimates.

**PASS:** https://github.com/Charlie-Wang-03/awards/actions/runs/38255501362
(3,408 jobs). The hole scanner still finds **exactly one** executable
sorry, now at *PlanarLowerBranchProofAdmittedWIP.lean* line 160.
Its axiom print honestly includes sorryAx.

**Critical outstanding gap:** the actual six-source payment and its
exact net-unpaid collision/unused-covered-sink equivalent are NOT
proved from real planar geometry. Even the eligible credit E_net
consists of ALREADY COVERED words. It is a valid algebraic credit
only after the exact sink/source identity, not a TRUE Boolean hole
or a newly unreserved dyadic profile surplus. The twin-rigid,
ascending/descending mixed-rigid, and projected-loss debts remain.
No award-level or upstream-ready conclusion is established.


## Actual collision requires incomparable bridge active palettes

**2026-10-12. A genuinely new structural collision restriction;
the original JSP-000404 is still OPEN in this fork.**

### Exact hard-source obstruction (2 independently checked Lean theorems)

File: `JSP000404Research/ResidualActualCollisionDistinctFlip.lean`.

A forward safe hard transport source Boolean word and a strict-rigid
reverse hard transport source word cannot be identical, by unique
hard-word carrier ownership and the opposite transportability flags
of their hard carriers.

Consequently, whenever their one-coordinate flip images are equal,
their chosen flip colours MUST be DIFFERENT. If the colours coincided,
flipping the common image back along that coordinate would make both
hard source words literally equal. This is a necessary condition on
actual image collisions, not a conjectured Hall payment.

Green targeted CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38259713597
(3,487 jobs; zero new `sorryAx`).

### Cross-active palette obstruction (3 independently checked theorems)

File: `JSP000404Research/ResidualActualCollisionCrossActive.lean`.

Let `p=(a,v)` be a forward-transportable hard carrier, and
`q=(b,z)` be a terminal strictly descending rigid hard carrier.
For an ACTUAL common transported image `w`, the unique residual
soft bridge has oriented endpoints `(b,v)`.

Writing `A_x=retainedActive C x`, and `c_f`, `c_r` for the
forward and reverse flip coordinates, the Lean kernel proves:

~~~text
c_f in A_b  A_v
c_r in A_v  A_b

THEREFORE

NOT (A_b SUBSET A_v)
AND
NOT (A_v SUBSET A_b).
~~~

The proof establishes the two positive cross-active memberships
by contradiction using the no-three-distinct-centres-can-cover-one-
Boolean-word theorem. If `c_f` were inactive at `b`, the ORIGINAL
forward hard source word would simultaneously belong to three
different retained completion cubes `Q_a,Q_v,Q_b`; the reverse
argument similarly uses `Q_b,Q_z,Q_v`.

This is stronger than flip-coordinate inequality, and applies
without any extra AngleCap hypothesis.

Green targeted CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38260728510
(3,488 jobs; all three theorem axiom prints exclude `sorryAx`).

### Exclude palette-comparable candidate bridge faces (5 theorems)

File: `JSP000404Research/ResidualIncomparableBridgePool.lean`.

Define `incomparableBridgeSoftCarriers` by FILTERING the original
oriented `forwardReverseBridgeSoftCarriers`, retaining ONLY those
soft carrier pairs `r=(b,v)` whose endpoint active sets are
mutually non-contained.

The actual full-forward/reverse and NET-UNPAID forward/reverse
collision sets BOTH lie in the union of the filtered overlap faces:

~~~text
actualCollision SUBSET incomparableBridgeSoftWords
netActualCollision SUBSET actualCollision
incomparableBridgeSoftWords SUBSET originalCandidateBridgeSoftWords
~~~

Moreover, if EVERY possible original candidate bridge happens to
have comparable active palettes, the ACTUAL collision set is empty.
This is a rigorously proved CONDITIONAL; no claim is made that
true planar AngleCap geometry automatically makes all candidates
comparable. The filter need not be proper in every instance.

A minor Lean-library naming issue in the emptiness corollary was
fixed by a direct `Finset` extensionality-and-contradiction proof.
No axiom or theorem hypothesis was added.

Green targeted CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38262013201
(3,489 jobs; five new theorem axiom prints have no `sorryAx`).

### Exact filtered dyadic mass and NET mobile bound (2 theorems)

Also in `ResidualIncomparableBridgePool.lean`.

Distinct candidate soft carrier overlap faces are pairwise disjoint,
and the original completion-cube intersection formula counts every
such face exactly. Therefore:

~~~text
card(incomparableBridgeSoftWords)
 = SUM_(r in incomparableBridgeSoftCarriers)
     2^card(commonRetainedInactive(r)).

netUnpaidForwardHardSourceMass + reverseStrictHardSourceMass
  + card(netUnusedEligibleCoveredSinkWords)
 <= card(singletonCompletionWords) + card(softOverlapCompletionWords)
    + SUM_(r in incomparableBridgeSoftCarriers)
        2^card(commonRetainedInactive(r)).
~~~

This is a **stronger source-side restriction** than the old bound
which used ALL potential bridge-soft carriers and discarded all
unused covered sink slots.

Green targeted CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38262369113
(3,226 jobs; both new theorem axiom prints exclude `sorryAx`).

### Genuine AngleCap specialization and WIP wiring (1 planar theorem)

File: `JSP000404Research/PlanarIncomparableBridgeCapacity.lean`.

The new theorem
`planar_net_mobile_mass_plus_unused_le_incomparable_bridge_dyadic`
derives all active-colour/exponent one-layer requirements from
the REAL planar `AngleCap`, `t=n+delta`, `0<=delta<1/2`,
and centre-projective-cycle assumptions, with no additional
geometric postulate. It then establishes the filtered dyadic
bound above on the actual planar residual colouring.

Green CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38262764725
(3,490 jobs; only `propext`, `Classical.choice`,
`Quot.sound` in the planar theorem's axiom audit).

The existing research-only WIP now imports the planar theorem and
records `hpaletteFilteredMobile` alongside the previous
`hnetPaymentFrontier`. Its end-to-end targeted regression
is green:
https://github.com/Charlie-Wang-03/awards/actions/runs/38263145132
(3,412 jobs).

The WIP audit STILL reports precisely ONE executable `sorry`
at `PlanarLowerBranchProofAdmittedWIP.lean:169`, and its
`#print axioms` STILL reports `sorryAx`.

**What remains mathematical:** The new incomparable-palette filter
eliminates many structurally IMPOSSIBLE collision carriers, but
does NOT establish that the filtered mass can be paid by actual
Boolean holes or genuinely unreserved profile surplus. In
particular, the twin, both mixed-rigid and projected-profile-loss
sources are not discharged. The next high-value target is to
derive a TRUE geometric bound (or explicit counterexample) on
the palette-INCOMPARABLE bridge configuration in real AngleCap
geometry, then connect it to a non-reusing true-hole/surplus
payment. The original JSP-000404 conclusion is NOT established,
and the admitted theorem must not be used as an upstream
prize-proof claim.


## New codimension-two palette obstruction and dyadic density budget

**2026-10-12 research increment; NO proof/disproof of the original JSP-000404 and NO new assumed geometric payment.**

### Two independent cross-active witnesses (8 Lean theorems)

New sorry-free module: JSP000404Research/ResidualIncomparableBridgeCodimension.lean.

For every candidate soft bridge r=(b,v) with incomparable retained-active endpoint palettes, the Lean kernel constructs TWO DISTINCT witnesses:

~~~text
cf in A_b \ A_v
cr in A_v \ A_b
cf != cr

card(A_b UNION A_v) >= 2
card(A_b UNION A_v) >= card(A_b) + 1
card(A_b UNION A_v) >= card(A_v) + 1

card(commonRetainedInactive(b,v)) + 2 <= n
card(commonRetainedInactive(b,v)) + card(A_b) + 1 <= n
card(commonRetainedInactive(b,v)) + card(A_v) + 1 <= n
~~~

This sharpens the qualitative incomparability obstruction to two independent Boolean dimensions and two separate per-endpoint free-coordinate losses. It requires no new AngleCap hypothesis.

The filtered candidate bridge carrier pool and actual NET unpaid forward/reverse collision set are BOTH empty for n <= 1. This settles only that collision component, not the six-source lower-branch conclusion.

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38265659015
(3,491 jobs PASS; eight theorem axiom prints exclude sorryAx).

### Dyadic quarter/half bounds and finite-carrier density (5 Lean theorems)

Same module, additional theorems:

~~~text
For every filtered bridge r=(b,v):

2^card(commonInactive(b,v)) <= 2^(n-2)

2 * 2^card(commonInactive(b,v))
  <= card(retainedCompletionWords(b))
2 * 2^card(commonInactive(b,v))
  <= card(retainedCompletionWords(v))

card(incomparableBridgeSoftWords)
  <= card(incomparableBridgeSoftCarriers) * 2^(n-2)

card(NET actual forward/reverse collisions)
  <= card(incomparableBridgeSoftCarriers) * 2^(n-2)

netUnpaidForwardHardMass + reverseStrictHardMass
  + card(netUnusedCoveredEligibleSinks)
 <= singletonCoveredMass + softCoveredMass
      + card(incomparableBridgeSoftCarriers) * 2^(n-2).
~~~

This identifies a concrete candidate geometrical carrier-COUNT problem instead of requiring the full weight of arbitrary overlap faces. The sink sets in this statement are ALREADY COVERED, NOT Boolean holes.

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38266203593
(3,227 jobs PASS; three mass lemmas);
https://github.com/Charlie-Wang-03/awards/actions/runs/38266577403
(3,227 jobs PASS; two net collision mass lemmas).
All five axiom audits exclude sorryAx.

### True planar AngleCap specialization and WIP wiring (1 theorem)

New module: JSP000404Research/PlanarIncomparableBridgeDensityCapacity.lean.

The certified planar_net_mobile_mass_plus_unused_le_incomparable_bridge_density theorem derives the original centre exponent and one-layer active-card budgets from actual AngleCap geometry and true projective cycles, then proves the quarter-density inequality above with NO extra geometric postulate.

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38266932182
(3,492 jobs PASS; only standard Lean axioms).

The sole admitted WIP now imports this planar module and retains the verified hpaletteQuarterMobile among its open-boundary inputs.

WIP CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38267340306
(3,414 jobs PASS). The scanner still finds EXACTLY ONE executable sorry, at JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean:179, and the dependent WIP theorem's axiom print still includes sorryAx.

### Essential still-open mathematics

The full six-source TRUE-hole/unreserved-profile-surplus payment does NOT follow from the proven collision codimension. We still lack a sufficiently strong geometric bound on the COUNT of incomparable bridge carriers and, especially, a non-reusing assignment of these plus the soft, rigid-twin, mixed-rigid and projected-loss debts to ACTUAL Boolean holes or genuinely unreserved surplus.

The singleton/soft eligible sink sets remain COVERED and cannot be reclassified as true holes. This work improves a quantified necessary collision budget but is not a proof or disproof of JSP-000404 and licenses no upstream award submission.


## Strict-rigid lower-exponent bridge half-mass bound

**2026-10-12: 6 NEW kernel-certified theorems; original
JSP-000404 remains unproved and undisproved.**

Modules:
- JSP000404Research/ResidualIncomparableBridgeLowerExponent.lean
- JSP000404Research/PlanarIncomparableBridgeLowerExponent.lean

The previous incomparable-bridge codimension bound measured each
remaining candidate soft bridge face against the full ambient cube,
giving 2^card(commonInactive(b,v)) <= 2^(n-2).

The stronger breakthrough in this increment measures the very same
face against its actual strict-rigid LOWER target b. By the literal
candidate-bridge definition, b is the lower endpoint of some genuine
strict descending rigid hard carrier q=(b,z). The already certified
one-layer rigid saturation theorem yields the exact identity

  projectedFree C b = exponent b = n - card(retainedActive C b).

Palette incomparability supplies an additional retained-active colour
on v absent from b. Hence, without ANY additional geometric
assumption, Lean now proves:

~~~text
For each incomparable bridge r=(b,v):

card(commonRetainedInactive(b,v)) + 1 <= exponent(b)

2 * 2^card(commonRetainedInactive(b,v)) <= 2^exponent(b)

0 < exponent(b)

2 * card(incomparableBridgeSoftWords)
  <= SUM_(r=(b,v) incomparable bridge) 2^exponent(b)

2 * card(NET actual forward/reverse sink collisions)
  <= SUM_(r=(b,v) incomparable bridge) 2^exponent(b).
~~~

This is an exponent-budget improvement over 2^(n-2) whenever the
actual lower target k(b) is small. Crucially, the sum is OVER
BRIDGE CARRIERS: several bridges can share the SAME lower endpoint,
so it is NOT an independent sum over strict rigid lower targets,
nor a proven injection to true Boolean holes or genuinely unreserved
profile surplus. Those payments remain wholly unresolved.

The abstract five theorems are imported by VerifiedOverlapRewire
and print only standard Lean axioms:
https://github.com/Charlie-Wang-03/awards/actions/runs/38273326744
(3,493 Lean jobs PASS, no new sorryAx).

The genuine planar theorem
planar_net_actual_collision_twice_le_strict_lower_target_sum
specializes the fifth inequality to actual injective plane points,
AngleCap, t=n+delta with 0<=delta<1/2, and their true
centre-projective-cycle exponents without adding hypotheses:
https://github.com/Charlie-Wang-03/awards/actions/runs/38273810920
(3,494 Lean jobs PASS, only propext/Classical.choice/Quot.sound).

The sole admitted WIP now imports this new planar module and
has the certified hbridgeLowerExponent available at the
six-source geometric payment boundary. Integrated CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38274243612
(3,416 jobs PASS). There is STILL exactly one executable sorry
in PlanarLowerBranchProofAdmittedWIP.lean at line 188,
and its axiom audit still reports sorryAx.

**Precise research frontier:** Prove a genuinely NON-REUSING
geometric aggregation over distinct saturated lower endpoints,
then connect that collision capacity with ALL remaining soft,
rigid-twin, mixed-rigid and projection-loss debt to ACTUAL true
Boolean holes and NET unreserved dyadic profile surplus.
An individual half-cube estimate cannot, on its own, pay the
same lower target repeatedly. This increment supplies a sharper
verified bound, NOT completion or disproof of JSP-000404.


## Exact unique strict shell ownership and two-bit bridge Hamming filter

**2026-10-12. Research-only progress on the actual collision subproblem.
The original JSP-000404 is NOT proved or disproved by this increment.**

### A. ACTUAL net collision: unique strict-rigid lower-shell ledger (5 Lean theorems)

Module: JSP000404Research/ResidualNetActualCollisionStrictShellFibre.lean

Let I_net be the exact intersection of the chosen globally injective
unpaid-forward-hard and reverse-strict-rigid sink images. For each
strict-descending rigid carrier q=(b,z), set shell(q)=Q_b \ Q_z
and I_q = I_net INTER shell(q).

The kernel certifies:

~~~text
I_net SUBSET U = union_(q strict) shell(q)

I_net = DISJOINT UNION_(q strict) I_q

card(I_net) = SUM_(q strict) card(I_q)

I_q SUBSET shell(q) INTER softOverlapCompletionWords

card(I_q)
  + card(shell(q) INTER singletonCompletionWords)
  <= 2^exponent(b) - 2^exponent(z).
~~~

The disjointness follows from the already certified strict-hard lower
cube separation and hard-carrier matching. This is a literal
NON-REUSING attribution of each actual collision word to exactly one
strict-rigid lower target, unlike the prior upper bound that summed a
full lower-target weight once PER BRIDGE and hence repeated lower b.
The shell capacity and singleton words are nevertheless COVERED,
not Boolean holes or newly available profile surplus.

Five axiom prints exclude sorryAx. Targeted CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38280332600
(3,495 Lean build jobs successful).

### B. ACTUAL collisions require two distinct retained-bit disagreements (3 theorems)

Module: JSP000404Research/ResidualActualCollisionTwoBitDisagreement.lean

The canonical forward hard source p=(a,v) and reverse strict rigid
source q=(b,z) have identical retained bits WITHIN each hard
carrier, by SameRetained(a,v) and SameRetained(b,z).
Their chosen individual flips c_f and c_r are provably distinct.

If their transported image words actually agree, the kernel proves:

~~~text
retainedBit(b, c_f) != retainedBit(v, c_f)
retainedBit(b, c_r) != retainedBit(v, c_r)
c_f != c_r

card({ c : Fin n | retainedBit(b,c) != retainedBit(v,c) }) >= 2.
~~~

The proof uses source completion membership, flipped target
completion membership, and the two hard carriers' identical retained
codes. An initial Lean failure was only a local-let normalization in
the final Finset-cardinality tactic; it was corrected using explicit
change expressions, without new hypotheses.

The Hamming-distance >=2 requirement is a NEW structural obstruction
that does not follow merely from palette incomparability.

Three theorem axiom prints exclude sorryAx. CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38281461703
(3,496 Lean build jobs successful).

### C. Doubly filtered BRIDGE pool: palettes AND actual bit disagreement (7 theorems)

Module: JSP000404Research/ResidualActualCollisionTwoBitBridgePool.lean

Define the doubly filtered oriented potential carrier pool B_2 to
contain r=(b,v) only when it was already a candidate
forward/reverse SOFT bridge with incomparable endpoint retained-active
palettes, AND the retained Boolean bit codes of b and v differ
in at least two positions.

The new theorems establish the literal inclusions:

~~~text
I_net SUBSET B_2_words
actual full-forward/reverse collision SUBSET B_2_words
B_2_words SUBSET incomparableBridgeSoftWords
incomparableBridgeSoftWords SUBSET originalBridgeSoftWords
~~~

Distinct soft residual carrier overlap faces remain disjoint.
Therefore there is also an EXACT mass equality:

~~~text
card(B_2_words)
  = SUM_(r in B_2_carriers)
      2^card(commonRetainedInactive(r)).
~~~

With E_net the already covered but UNUSED singleton/soft sink words:

~~~text
netUnpaidForwardHardMass + reverseStrictHardMass + card(E_net)
  <= card(singletonCoveredWords) + card(softCoveredWords)
     + SUM_(r in B_2_carriers)
         2^card(commonRetainedInactive(r)).
~~~

Additionally, if ALL formerly incomparable candidate bridge
endpoint code pairs have Hamming distance <=1, the actual full
forward/reverse intersection is empty. This is an explicitly
CONDITIONAL statement; no claim is made that every genuine planar
AngleCap instance has that property. The filtered set may
coincide with the older candidate set in some instances.

Seven theorem axiom prints exclude sorryAx. CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38281903499
(3,497 Lean build jobs successful).

### D. True planar AngleCap specialization and single WIP boundary (1 theorem)

Module: JSP000404Research/PlanarActualCollisionTwoBitBridgeCapacity.lean

The new planar_net_mobile_mass_plus_unused_le_two_bit_bridge_dyadic
obtains the exponent and active-colour one-layer budgets from
the REAL injective planar point map, AngleCap, t=n+delta,
0<=delta<1/2, and true centre projective cycles, then certifies
the above two-bit BRIDGE mass bound in the actual residual model.
No extra geometric hypothesis or unverified collision-matching
axiom is introduced.

The sole WIP imports this planar lemma as
htwoBitFilteredMobile and preserves the previously verified
lower-exponent and non-reusing lower-shell components.

Final integrated CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38282485407
(3,499 Lean jobs PASS). The planar lemma has only
propext, Classical.choice, Quot.sound in its axiom report.

The WIP scanner still records EXACTLY ONE executable sorry
in PlanarLowerBranchProofAdmittedWIP.lean line 199.
The WIP conclusion's #print axioms still includes sorryAx.

### E. Exact remaining proof obligation: still genuine geometry, not bookkeeping

The new partition prevents REUSING any strict-rigid lower shell
when accounting for ACTUAL mobile transport collisions.
The two-bit filter eliminates all Hamming-0/1 and comparable
palette candidate soft bridge faces.

These facts DO NOT prove that true Boolean holes plus genuinely
UNRESERVED dyadic profile surplus pay:
- all soft-overlap debt,
- net unpaid forward mobile hard sources,
- reverse strict-rigid hard sources,
- equal-exponent rigid twin targets,
- ascending and descending mixed-rigid target debt, and
- projected-profile loss.

Indeed all strict-rigid lower shell positions, singleton sinks,
and soft bridge sinks are ALREADY COVERED Boolean words. The
verified local collision budget cannot be rebranded as the
missing global true-hole payment.

The decisive next mathematical step must connect the remaining
doubly filtered actual collisions and the other outstanding
rigid/mixed/loss sources to independent TRUE-hole or unreserved-
surplus capacities, or else exhibit a genuine planar counterexample.
This work cannot be presented as an upstream award proof.

## Two-flip Boolean square: local exterior injection and explicit third-centre payment


### 1. Opposite corner of an actual forward/reverse hard image collision

New Lean module: ResidualActualCollisionTwoFlipDiagonal.lean.

Let p=(a,v) be the forward hard carrier, q=(b,z) the reverse
strict-rigid hard carrier, w the ACTUAL common sink image in
Q_b INTER Q_v, and cf/cr the distinct chosen transport colours.
We have cf active at b and inactive at v; cr inactive at b
and active at v. Define d(w)=flip_cf(flip_cr(w)).

Certified in Lean:

~~~text
double_flip(cf,cr) is INJECTIVE
d(w) NOT-IN Q_b and d(w) NOT-IN Q_v

d(w) in GLOBAL Boolean holes
OR
there exists c != b and c != v with d(w) in Q_c.
~~~

This is an EXACT third-centre obstruction, NOT a proof that the
opposite square corner is globally uncovered. An initial Lean
type-inference failure was fixed by explicitly binding the Boolean
word as Fin n -> Bool without adding any hypotheses.

### 2. Whole-face two-cube exterior injection

New Lean module: ResidualIncomparableBridgeExteriorCapacity.lean.

If endpoint retained-active palettes are incomparable, choose
cross-active coordinates cf and cr and double-flip each word
in the entire overlap face. The map is injective into the
exterior of the TWO endpoint completion cubes:

~~~text
card(Q_b INTER Q_v)
 <= card(BooleanUniv \ (Q_b UNION Q_v)).

For every incomparable candidate bridge r=(b,v):
2^card(commonRetainedInactive(b,v))
 <= card(BooleanUniv \ (Q_b UNION Q_v)).
~~~

This is a genuine numerical capacity theorem for explicit
two-cube EXTERIOR words, and also applies to the Hamming-two
filtered candidate bridge pool. It assumes no new AngleCap axiom.

### 3. Local true-hole versus external-third-centre ledger

New Lean module: ResidualBridgeDiagonalTrueHoleLedger.lean.

Write C=union_all_centres Q_x (the global COVERED word set),
H=BooleanUniv \ C (the GLOBAL TRUE HOLES),
E(b,v)=BooleanUniv \ (Q_b UNION Q_v), and
X(b,v)=E(b,v) INTER C (the EXTERNALLY COVERED exterior).

Lean proves, for incomparable endpoint palettes:

~~~text
card(Q_b INTER Q_v) <= card(H) + card(X(b,v)).

Every word in X(b,v) is covered by some c != b,v.

CONDITIONAL: if X(b,v)=EMPTY, then
  card(Q_b INTER Q_v) <= card(H).
~~~

The last theorem is deliberately conditional. We have NOT proved
that planar AngleCap eliminates all third-centre covers. The
external-cover mass X cannot be discarded or renamed unreserved
dyadic surplus. Furthermore, separate local injections cannot be
summed globally without disjointness/non-reuse.

A first Lean error was an unavailable Finset emptiness lemma
name; finite-set extensionality repaired the proof without
new premises.

### 4. Audited evidence

Seven new theorems in the first two modules are Lean-checked
with NO sorryAx in 3,500 successful build jobs:
https://github.com/Charlie-Wang-03/awards/actions/runs/38285261097

Three new true-hole ledger theorems are Lean-checked
with NO sorryAx in 3,501 successful build jobs:
https://github.com/Charlie-Wang-03/awards/actions/runs/38286241524

VerifiedOverlapRewire.lean imports all three modules. The
research-only WIP imports the true-hole obstruction explicitly
but intentionally retains the original single sorry.

### 5. Remaining mathematical frontier

To turn double-flipped exterior words into genuine globally
available Boolean holes or NET unreserved profile surplus, one
must bound or independently pay X(b,v), and avoid reusing hole
targets across DIFFERENT bridges. Genuine planar AngleCap may
constrain third-centre covering configurations, but this has
NOT yet been established.

In addition, the rigid-twin, both mixed-rigid, projected-loss,
other soft-overlap and both net mobile-hard debts must be paid
together in the complete six-source inequality. Original
JSP-000404 is NOT yet proved or disproved.


## Opposite-bit external blockers and exact targeted diagonal hole deficit

**2026-10-13. Six NEW kernel-certified Lean theorems.
NO complete proof or disproof of JSP-000404.**

### 1. Third-centre blocker MUST have the OPPOSITE retained bit

New module:
JSP000404Research/ResidualTwoFlipOppositeBitBlocker.lean.

Let w lie in Q_b INTER Q_v. Choose cross-active
flip colours cf in A_b \ A_v and cr in A_v \ A_b,
and let d = flip_cf(flip_cr(w)). Previous Lean
lemmas show d OUTSIDE Q_b UNION Q_v. Any new centre
c with d in Q_c must satisfy

~~~text
(cr in A_c AND retainedBit(c,cr) = NOT retainedBit(v,cr))
OR
(cf in A_c AND retainedBit(c,cf) = NOT retainedBit(b,cf)).
~~~

Proof reuses the certified two-flip blocker-active-one,
bit-at-first and bit-at-second lemmas with the precise
cr-then-cf flip order. It is a kernel-checked
orientation/bit constraint, not a conjectural
AngleCap exclusion.

The same module establishes a CONDITIONAL genuine
GLOBAL true-hole injection from the WHOLE overlap cube:
if every other centre c != b,v has a matching
(not opposite) bit whenever it activates cr or cf,
then every selected double-flip image is a true hole:

~~~text
card(Q_b INTER Q_v) <= card(global_TRUE_holes).
~~~

That condition is much WEAKER than the former
"entire exterior E(b,v) has no global coverage"
sufficient condition. It is still not known to follow
from the genuine planar AngleCap and centre cycles.

CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38350749459
(3,502 successful Lean jobs; three theorems with
standard axioms only, no sorryAx).

### 2. EXACT target-image partition, not whole exterior

New module:
JSP000404Research/ResidualTwoFlipTargetedTrueHoleLedger.lean.

Fix the same cf,cr, and let
F = Q_b INTER Q_v,
D = {flip_cf(flip_cr(w)) : w in F},
H = global TRUE holes,
K = global coveredCompletionWords.

The double-flip map is injective; its image partitions
EXACTLY as

~~~text
card(F) = card(D INTER H) + card(D INTER K).
~~~

Therefore, rigorously,

~~~text
card(F) <= card(H) + card(D INTER K).
~~~

This bound improves the PREVIOUS coarse external-centre
term card((univ \ (Q_b UNION Q_v)) INTER K):
only actually reachable double-flip diagonal images
can obstruct genuine hole payment.

More significantly, EVERY selected covered diagonal
d in D INTER K has an original overlap word w and
an EXTERNAL centre c != b,v covering d, where c
exhibits the OPPOSITE bit at cr or cf as above.

An initial Lean run had two script-level failures:
an unexpanded set-complement case split and an
inappropriate goal transformation at the final
cardinal arithmetic step. Both were corrected
with explicit by_cases and a goal-local change;
no theorem statements or hypotheses changed.

CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38351334101
(3,503 successful Lean jobs, three theorem
axiom checks no sorryAx).

### 3. WIP integration and precise remaining obstruction

The sole admitted file
JSP000404Research/PlanarLowerBranchProofAdmittedWIP.lean
now imports the targeted true-hole ledger. Its
comments state the exact local diagonal identity
and explicitly warn that the globally COVERED
diagonal targets are NOT true holes or surplus.

Integrated targeted CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38351612317
(3,428 successful Lean jobs; no compile errors).
Scanner: EXACTLY ONE executable sorry at line 219.
The WIP theorem's axiom audit STILL contains sorryAx.

The frontier is now more specific:

- Eliminate or bound the OPPOSITE-BIT external-centre
  obstruction on selected diagonal images, using real
  planar AngleCap geometry, rather than all possible
  exterior third-centre coverage.
- Establish a GLOBAL NON-REUSING assignment across
  DIFFERENT bridge faces; per-bridge double-flip maps
  are injective individually, but their target images
  may collide across faces.
- Pay remaining soft overlap, forward/reverse net
  mobile hard, rigid twins, both mixed rigid sources,
  and projected-profile loss with TRUE Boolean holes
  and genuinely UNRESERVED dyadic profile surplus.

The local exact identity and conditional injection
do NOT discharge this global geometric payment.
No upstream prize solution is asserted.


## Actual collision diagonal: original hard-source blockers and fifth-centre frontier

**2026-10-13 research increment. JSP-000404 remains OPEN.**

Module: JSP000404Research/ResidualTwoFlipSourceEndpointBlocker.lean
(the new module is imported by the independently verified
VerifiedOverlapRewire.lean; the sole admitted WIP also imports it).

Let the actual globally injective forward and reverse hard transports
collide at covered sink word w. Write their original hard carriers as
p=(a,v), q=(b,z), their source words as x,y, their distinct chosen
retained flip coordinates as cf,cr, and their double-flip diagonal as

  d = flip(cf, flip(cr,w)).

The Lean kernel now proves exact identities:

~~~text
w = flip(cf,x) = flip(cr,y)
d = flip(cr,x) = flip(cf,y)
~~~

The two identities hold for ACTUAL common transport images, not
arbitrary candidate soft bridges.

### A. Two CONCRETE original-hard-source blockers (6 Lean theorems)

If cr is INACTIVE at a, the original forward-hard source centre a
itself covers d: d in Q_a.

If cf is INACTIVE at z, the original reverse-hard source centre z
itself covers d: d in Q_z.

Thus, a TRUE GLOBAL HOLE at d forces BOTH additional cross-activity
conditions:

~~~text
cr in retainedActive(a)
AND
cf in retainedActive(z).
~~~

These conditions are NECESSARY, never proved to hold universally
from AngleCap, and are NOT sufficient to make d a global hole.

The first six Lean theorems include the independent commuting-flip
identity, the two exact source-diagonal equations, both concrete
source endpoint coverage lemmas, and the true-hole necessary
cross-activity criterion.

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38356011212
(3,504 jobs PASS; all six theorem axiom checks have no sorryAx).

The WIP import and comments explicitly retain the fact that a
two-cube exterior word can be COVERED by its original hard-source
endpoints; it is not independently usable profile surplus.

WIP CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38356345189
(3,429 jobs PASS). Exactly ONE executable sorry is still at
PlanarLowerBranchProofAdmittedWIP.lean:230, and the WIP theorem
still has sorryAx in its axiom report.

### B. Fifth-centre exclusion and exact iff (3 more Lean theorems)

Under BOTH source-side cross-active conditions just specified, the
opposite diagonal is provably outside ALL FOUR original hard
carrier completion cubes, including those source endpoints:

~~~text
d NOT IN Q_a
d NOT IN Q_v
d NOT IN Q_b
d NOT IN Q_z.
~~~

Consequently, if d is nevertheless globally covered, some centre c
different from EACH of a,v,b,z must cover it.

The strongest new lemma establishes a precise mathematical IFF:

~~~text
Under both source-side cross-active conditions,

d IN (univ \ coveredCompletionWords)
 IFF
for every centre c with
  c != a, c != v, c != b, c != z,
  d NOT IN Q_c.
~~~

Hard carrier vertex matching already guarantees the two hard pairs
are distinct and vertex-disjoint, so any such external c is
literally a FIFTH distinct vertex (or later).

CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38356554751
(3,240 jobs PASS; all-four-exterior and fifth-centre existence
theorems have no sorryAx).
CI: https://github.com/Charlie-Wang-03/awards/actions/runs/38356880695
(3,240 jobs PASS; exact true-hole iff no fifth-centre theorem
has no sorryAx). The sole WIP sorry remains at line 230.

### C. What is actually unresolved

This is a GENUINE sharpening of the missing true-hole outlet
condition, not a proof of the outlet itself.

For an ACTUAL hard sink collision w to be charged to the particular
double-flip diagonal d as a genuine true Boolean hole, the two
source-side cross-activities must first hold, and then every
POSSIBLE fifth-centre covering of d must be excluded.

No current theorem establishes either global requirement
automatically from real planar AngleCap geometry. Even proving
the local fifth-centre exclusion for each collision would NOT
provide a globally injective hole allocation across distinct
hard collision carriers, nor pay the other soft, rigid-twin,
mixed-rigid, and projected-profile-loss debts.

Do not count d as a true hole without those conditions, do not
double-book global holes across collision carriers, and do not
remove the one executable sorry in the absence of a complete
six-source payment proof. The original JSP-000404 theorem
remains unproved and undisproved by this downstream branch.

## Exact actual-collision diagonal obstruction equivalence (2026-10-13)

Module: `JSP000404Research/ResidualActualCollisionDiagonalExactObstruction.lean`.
Both new theorem statements are proved in Lean 4 without `sorry` or new
mathematical assumptions; they are imported by the independent
`VerifiedOverlapRewire.lean` umbrella. They concern an ACTUAL common
sink of the globally injective forward and reverse hard transports.

For original hard carriers `p=(a,v)` and `q=(b,z)`, with forward and
reverse flip colours `cf,cr`, let `d=flip(cf,flip(cr,w))` be the
opposite diagonal of their common sink `w`. The certified exact
covering criterion is

```text
d IS GLOBALLY COVERED
  IFF (cr NOT retainedActive(a))
   OR (cf NOT retainedActive(z))
   OR (EXISTS c OUTSIDE {a,v,b,z} WITH d IN Q_c).

d IS A GLOBAL TRUE HOLE
  IFF (cr IN retainedActive(a))
  AND (cf IN retainedActive(z))
  AND (FOR EVERY c OUTSIDE {a,v,b,z}, d NOT IN Q_c).
```

Proof method: combine the previous two constructive original-source
coverage lemmas, the certified fifth-centre theorem under both
cross-active conditions, and the earlier conditional true-hole IFF.
The new statements do NOT postulate that cross-activity always holds
or that fifth-centre coverage is absent. In particular, there is no
proved globally injective allocation of diagonals to true holes
across different actual collisions, and the remaining twin/mixed/
soft/projected-loss payments are NOT discharged.

Original new-module CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38367805581
PASS (3,241 Lean jobs). Both `#print axioms` outputs list
`[propext, Classical.choice, Quot.sound]`; NO `sorryAx`.
The only executable admitted WIP `sorry` remains in
`PlanarLowerBranchProofAdmittedWIP.lean`; it is not replaced
by this local equivalence. JSP-000404 is NOT solved.

## Fifth-centre opposite-bit signature at ACTUAL hard collision (2026-10-13)

Follow-up theorem:
`actual_collision_diagonal_covered_iff_source_block_or_opposite_fifth`
in the SAME sorry-free
`ResidualActualCollisionDiagonalExactObstruction.lean` module.

This strengthens the exact local classification further. If an
actual hard sink-collision diagonal `d` is globally COVERED,
one of these three cases holds, and each case is sufficient:

1. `cr` is INACTIVE at the forward original lower source `a`,
   whose completion cube then explicitly covers `d`.
2. `cf` is INACTIVE at the reverse original upper source `z`,
   whose completion cube then explicitly covers `d`.
3. A genuinely FIFTH-OR-LATER centre `c` covers `d`, AND
   this `c` must activate a cross-flip coordinate with the
   OPPOSITE retained Boolean bit relative to its bridge endpoint:
   `(cr active at c, bit(c,cr)=NOT bit(v,cr))` OR
   `(cf active at c, bit(c,cf)=NOT bit(b,cf))`,
   with bridge endpoints `(b,v)` equal to
   (reverse rigid LOWER, forward hard UPPER).

The proof uses the pre-existing certified actual-bridge
cross-activity and bridge-endpoint coverage, then applies the
two-flip opposite-bit blocker lemma to the exact FIFTH witness.
It introduces NO new hypotheses or custom axioms. In the
reverse direction the explicit coverage witness itself suffices.

Lean CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38368480720
PASS (3,241 build jobs). Its axiom set is the ordinary
`[propext, Classical.choice, Quot.sound]`; zero `sorryAx`.

**Scope firewall:** this exact opposite-bit signature is a
NECESSARY characteristic of a covered fifth-centre diagonal.
It DOES NOT show that such a fifth centre cannot exist under
AngleCap; it DOES NOT globally allocate unique holes to
distinct actual collisions. It DOES NOT discharge the sole
six-source true-hole plus unreserved-surplus payment `sorry`,
and does not complete the upper branch or JSP-000404.


## Verified four-coordinate rigidity and conditional cross-pair nonreuse (2026-10-13)

New independent module:
`JSP000404Research/ResidualTwoFlipDiagonalGlobalCollisionRigidity.lean`.
It imports the existing EXACT actual-collision blocker classification,
and the new source is imported by the sorry-free
`JSP000404Research/VerifiedOverlapRewire.lean` umbrella.

For any Boolean words `w,z : Fin n -> Bool` and any two (possibly
DIFFERENT) ordered flip pairs `(cf1,cr1)`, `(cf2,cr2)`, if

```text
flip(cf1, flip(cr1,w)) = flip(cf2, flip(cr2,z)),
```

then the SOURCE words agree at EVERY coordinate outside
`{cf1,cr1,cf2,cr2}`. Therefore disagreement at any FIFTH
unflipped coordinate guarantees the two diagonal targets differ.
This is a proved unconditional necessary condition for
cross-pair double-flip target collision, not a geometric
AngleCap exclusion.

The five newly certified theorems are:

1. `double_flip_target_eq_source_agree_outside_four`.
2. `double_flip_targets_ne_of_source_diff_outside_four`.
3. `fixed_two_flip_hole_capacity`: a fixed double-flip map is
   injective on ANY source set, so if every target lies in a
   specified hole set H, source cardinality is at most |H|.
4. `two_flip_images_disjoint_of_four_coordinate_separation`:
   two source classes with possibly DIFFERENT fixed flip pairs
   have DISJOINT diagonal image sets if every cross-class
   source pair differs at some coordinate outside the union
   of the four flips.
5. `separated_two_flip_classes_joint_hole_capacity`: under
   the same cross-class separation PLUS genuine hole membership
   of BOTH classes' diagonal targets, the exact NON-REUSING
   bound `|S1| + |S2| <= |H|` holds.

Regression evidence:
- Initial three theorems: https://github.com/Charlie-Wang-03/awards/actions/runs/38377898759
  — 3,242 build jobs PASS, no new `sorryAx`.
- Cross-pair disjointness and joint hole capacity:
  https://github.com/Charlie-Wang-03/awards/actions/runs/38378284080
  — 3,242 build jobs PASS, no new `sorryAx`.

**Open gates, not implied by the proved lemmas:**
- The source-separation premise is NOT known to follow from the
  ACTUAL planar `AngleCap` data for different collision classes.
- True-hole status of the actual two-flip diagonals still requires
  both cross-source activities and exclusion of all fifth-or-later
  opposite-bit external blockers. Those requirements have not
  been proved universally from real planar geometry.
- The five new theorems provide a CONDITIONAL two-class allocation,
  NOT a general global injection or six-source payment.
- The single executable `sorry` in
  `PlanarLowerBranchProofAdmittedWIP.lean` remains genuine and
  must not be discharged by treating conditional hypotheses
  as geometric facts. The upper branch and full JSP-000404
  remain OPEN.

The two new steps therefore isolate the exact required
cross-pair nonreuse mechanism more sharply, but DO NOT
reduce the WIP `sorry` count.


## Exact ACTUAL NET-collision canonical diagonal global ledger (2026-10-13)

This step moves beyond the conditional fixed-flip-pair
source-separation lemmas. Every source is a GENUINE NET
forward/reverse hard-image collision word, not a hypothetical
bridge candidate. The two ORIGINAL hard transport sources
are certified unique by the globally injective forward and
strict-descent reverse maps; their carrier flip colours determine
one canonical, source-dependent double-flip diagonal.

### New sorry-free modules (17 named theorems total)

- `ResidualNetCollisionVariableDiagonalLedger.lean`
  (3 theorems): arbitrary variable-colour exact partition
  into DISTINCT global true-hole diagonals, DISTINCT globally
  covered diagonals and exact duplicate-image cardinal loss;
  source-dependent equal-diagonal four-coordinate rigidity.
  CI https://github.com/Charlie-Wang-03/awards/actions/runs/38387421192
  PASS, 3,243 build jobs.
- `ResidualNetCollisionCertifiedDiagonalWitness.lean`
  (4 theorems): each actual NET collision has a witnessed
  forward and reverse original hard source, each unique by
  its respective verified global injection. Hence the
  genuine chosen flip coordinates of each collision are
  unambiguous.
- `ResidualNetCollisionCertifiedGlobalLedger.lean`
  (2 theorems): the same exact three-way accounting on the
  ACTUAL source-dependent canonical diagonal map, plus
  unconditional hole-capacity bound retaining both
  unpaid obstruction terms.
- `ResidualNetCollisionCertifiedBlockerClassification.lean`
  (2 theorems): covered CANONICAL diagonals satisfy the exact
  source-side cross-inactivity or FIFTH-centre opposite-bit
  signature IFF; every distinct covered target has a
  real source collision witness and a concrete blocker.
- `ResidualNetCollisionCertifiedMobilePayment.lean`
  (3 theorems): substitute the canonical hole/blocker/duplicate
  partition into the independently established exact NET
  forward+reverse mobile-source conserved mass. This
  removes the formerly opaque actual-sink-collision term
  and gives a formal IFF for any proposed net payment.
- `ResidualNetCollisionCertifiedDuplicateWitness.lean`
  (3 theorems): POSITIVE actual duplicate-image debt implies
  two DISTINCT original NET collision sinks with the SAME
  canonical target, and the sinks agree at EVERY coordinate
  outside their four ACTUAL chosen original transport colours.
  CI https://github.com/Charlie-Wang-03/awards/actions/runs/38389064306
  PASS, 3,247 build jobs.

The first 14 certified theorems are jointly compiled with both
the sorry-free `VerifiedOverlapRewire` umbrella and the sole
admitted WIP via
https://github.com/Charlie-Wang-03/awards/actions/runs/38388685391
PASS, 3,512 build jobs. During development a missing unfolding
of `netCollisionCertifiedDiagonal` caused an actual Lean type error;
it was fixed by explicitly unfolding the definition. No new
`sorry` or ad-hoc axiom was introduced in the independent modules.

### New exact global equation

Write:
- `F` = NET unpaid forward movable hard SOURCE words;
- `R` = strict-descent reverse rigid hard SOURCE words;
- `U` = unused singleton-or-soft COVERED transport sink words;
- `S` = singleton-covered words, `T` = soft-overlap words;
- `I` = actual NET forward/reverse sink collision set;
- `D` = set of DISTINCT canonical double-flip diagonal targets
  with actual flip colours uniquely determined by `I`;
- `H` = TRUE global Boolean holes, `K` = globally covered
  Boolean words;
- `E` = `|I| - |D|`, the EXACT nonnegative global multiple-hit
  loss of the canonical diagonal mapping.

Then Lean proves, UNCONDITIONALLY at residual one-layer level,

```text
|F| + |R| + |U| = |S| + |T| + |D intersect H|
                                 + |D intersect K| + E.
```

Every term has unique set-level provenance. In particular,
`D intersect H` may be charged only once, while `D intersect K`
cannot be called holes, and `E` cannot be dropped on grounds
of unproved global injectivity.

The exact covered-diagonal IFF identifies the two ORIGINAL
source-side cross-inactivity blockers plus opposite-bit
fifth-centre coverage. Positive `E` has been reduced to
a SPECIFIC pair of distinct actual collision sink words with
the same target, differing at no coordinate outside their
four chosen flip colours.

### Remaining genuinely open gates

1. Either globally exclude (under actual planar AngleCap)
   the certified source-side/fifth-centre COVERED blockers
   OR pay them from genuine, NON-REUSED available resources.
2. Either exclude the exact four-colour duplicate-source
   witness pairs OR pay their multiplicity debt without
   counting a true hole twice.
3. Integrate those credits with independent soft-overlap,
   terminal equal-exponent twin, ascending/descending mixed
   rigid, and projected-loss debts. The right-hand profile
   surplus MUST be literally unreserved after all prior
   hard/mixed reservations.

**Status:** a genuine tightening and better literal provenance
of the ACTUAL net mobile-source payment obligation, NOT a
proof of the final six-source inequality. The admitted WIP
still has exactly one executable `sorry`. No completed proof
or counterexample to full JSP-000404 is claimed.


## Exact 2/4-bit actual NET canonical duplicate obstruction (2026-10-13)

This step CLOSES a further combinatorial subgap for the ACTUAL
canonical diagonal map. It strengthens the previous necessary
`outside-four coordinates agree` property to an EXACT equality
and a strict Hamming-distance dichotomy, with no added geometric,
source-separation, hole-coverage, or Hall hypotheses.

Let `s,t` be two genuine NET collision sink words; each has
a UNIQUE pair of original hard source carriers and the
canonically selected two DISTINCT flip colours. Let `A_s,A_t`
denote the corresponding unordered 2-colour sets, and let
`D(s),D(t)` be their certified canonical opposite diagonals.

New verified theorem statements:

1. `distinct_two_flip_coordinate_eval`: a double flip toggles
   precisely the two chosen distinct coordinates.
2. `two_flip_target_eq_source_diff_iff_pair_exclusive`:
   if two double-flipped targets coincide, then a source
   coordinate differs IFF it is contained in exactly one
   of the two unordered flip-colour supports.
3. `two_flip_equal_target_exact_difference_set`:
   `{i | w(i) != z(i)} = A_w △ A_z` exactly, not just
   subset-of-four.
4. `two_flip_equal_target_same_support_source_eq`:
   coinciding diagonals and identical UNORDERED flip-colour
   supports imply the same original source, including a
   reversal/swapping of colour roles.
5. `net_collision_certified_forward_reverse_colours_distinct`:
   the two actual canonical colours are DISTINCT, deduced
   from existing independently proved hard-source injection.
6. `net_collision_canonical_diagonal_exact_difference_support`:
   exact difference-set identity specialized to actual NET
   collision sources, using the UNIQUE original carriers.
7. `net_collision_canonical_same_target_same_unordered_pair_eq`:
   SAME unordered source pair and same target => same actual
   NET collision sink. Canonical diagonal transport is
   injective WITHIN every fixed unordered pair class.
8. `pair_symmetric_difference_card_zero_two_four`:
   a symmetric difference of two 2-element sets always
   has cardinality 0, 2 or 4.
9. `two_flip_equal_target_distinct_sources_hamming_two_or_four`:
   two DIFFERENT Boolean sources mapping to the same
   double-flip target have Hamming distance exactly TWO
   or FOUR; no odd distance and no zero-distance case.
10. `net_collision_canonical_support_fibre_injective`:
    actual NET canonical diagonals are injection on each
    fibre of their unordered support selector.
11. `net_collision_positive_duplicate_cross_support_hamming_two_or_four`:
    positive genuine global canonical duplicate debt
    witnesses DISTINCT actual NET collisions `s != t` with
    `D(s)=D(t)`, `A_s != A_t`, and `d_H(s,t) = 2 or 4`.

Lean source modules, all sorry-free:

- `ResidualTwoFlipExactSymmetricDifference.lean`
- `ResidualNetCollisionExactFlipSupport.lean`
- `ResidualTwoFlipExactHammingCases.lean`
- `ResidualNetCollisionExactHammingObstruction.lean`

Lean checks:
- GitHub Actions https://github.com/Charlie-Wang-03/awards/actions/runs/38401329370
  PASS (3,249 jobs) and all 7 initial theorem axiom audits
  exclude `sorryAx`.
- GitHub Actions https://github.com/Charlie-Wang-03/awards/actions/runs/38402258343
  PASS (3,251 jobs) for 4 additional Hamming/canonical
  witness theorems; `sorryAx` absent.
- Earlier failing iterations found a set-difference syntax
  escaping issue, reversed conjunction in a Lean goal,
  and an invalid reference to `Finset.not_mem_empty`.
  They were actually fixed; no `sorry`, `axiom`,
  or unrelated source mutation was introduced.

**Important scope firewall:** This is a mathematically real
restriction on the shape of the ACTUAL global duplication
obstruction, not its elimination. The hypothesis `E_D > 0`
is NOT disproved. Cross-support canonical duplicates
at Hamming 2 or Hamming 4 are NOT shown impossible in real
planar `AngleCap`. Covered canonical diagonals still have
source-side or fifth-centre opposite-bit blockers. Those
and duplicate-image debts remain uncharged; moreover twin
rigid, mixed rigid, soft and profile-loss terms need honest
nonreusing payment. The sole admitted WIP `sorry`
and the full JSP-000404 problem remain OPEN.


## Canonical NET diagonal multiplicity: exact shared colours and choose-two cap (2026-10-13)

New, sorry-free Lean source modules:
- `JSP000404Research/ResidualNetCollisionSupportOverlapLaw.lean`:
  four theorems, including the exact per-pair conservation identity,
  the 2-bit/common-1-colour IFF, and the 4-bit/disjoint-colours IFF.
- `JSP000404Research/ResidualNetCollisionSupportFibreMultiplicity.lean`:
  global injection of `(actual canonical diagonal, unordered TWO-colour
  support)`; aggregate choose-two multiplicity bound; and the
  fixed-diagonal SOURCE FIBRE choose-two cardinal bound.

Let `I` denote the GENUINE NET forward/reverse hard collision sink set,
`D` the actual canonical double-flip target map with selected colours
certified by UNIQUE original hard source carriers, and
`A_w` the unordered support of two original transport flip colours.

Whenever `D(w)=D(z)`, the new Lean proofs establish the EXACT equality

```text
HammingDistance(w,z) + 2 * card(A_w intersect A_z) = 4.
```

So Hamming distance TWO is EQUIVALENT to exactly ONE shared colour.
Hamming distance FOUR is EQUIVALENT to DISJOINT unordered colour pairs.
The already certified positive duplicate witness is therefore
restricted to either a 3-colour one-shared-coordinate pattern
or a 4-colour disjoint-pair pattern. This is a **source-native**
classification and does not assume any new AngleCap property.

The function `w ↦ (D(w),A_w)` is GLOBALLY injective on the ACTUAL
NET collision set, hence the remaining reuse of any one canonical
diagonal is strictly bounded by the number of available unordered
two-colour supports:

```text
for each d: |{ w in I | D(w)=d }| <= Nat.choose n 2
globally:   |I| <= |image(D)| * Nat.choose n 2.
```

This does NOT charge source words to true holes: `image(D)`
includes globally covered diagonal words, which must NOT be counted
as available global holes or genuinely unreserved dyadic surplus.
Nor does a multiplicity upper bound prove the duplicate-image debt
is ZERO or show how to pay it.

Build evidence for the overlap-law module:
https://github.com/Charlie-Wang-03/awards/actions/runs/38405980972
PASS (3,442 jobs); no added `sorryAx`.
Build evidence for initial choose-two pair injection and total
multiplicity bound:
https://github.com/Charlie-Wang-03/awards/actions/runs/38406630292
PASS (3,253 jobs); no added `sorryAx`.
The enhanced per-target fibre theorem is also imported into
`VerifiedOverlapRewire.lean` for independent checking.

**Still open:** under actual planar AngleCap, exclude or pay the
3-colour and 4-colour distinct-source/reused-diagonal motifs;
exclude or pay cross-inactivity/fifth-centre opposite-bit covered
diagonal obstructions; and integrate the truly non-reused twin,
mixed-rigid, soft and projected-loss debts against literal global
Boolean holes and genuinely unreserved profile surplus.
The admitted six-source global inequality and full JSP-000404
remain unproved; the unique WIP `sorry` stays intentionally.


## Exact source-fibre duplicate-debt and covered/uncovered split (2026-10-13)

The previous global canonical NET collision loss `E_D = |I| - |D(I)|`
was a correct but coarse cardinal difference. Two additional genuinely
sorry-free Lean modules now localize **every unit** of that debt to its
actual target fibre:

- `JSP000404Research/ResidualNetCollisionExactFibreDebt.lean`:
  a general finite-map theorem and its specialization to the
  unique-source canonical NET collision diagonal.
- `JSP000404Research/ResidualNetCollisionFibreDebtPartition.lean`:
  a checked complementary-set sum partition, exact actual debt split
  by true-hole versus globally covered targets, and a completely
  explicit replacement of the duplicate term in the NET
  forward/reverse mobile source conservation identity.

Define `F_d := {w in I | D(w) = d}`, where `I` is the genuine
NET collision sink set and `D` is its certified source-dependent
double-flip map. Define `H_D` as DISTINCT images lying in global
Boolean TRUE holes and `K_D` as DISTINCT images lying in GLOBAL
covered words. Lean now proves:

```text
E_D = sum_(d in D(I)) (|F_d| - 1)
    = sum_(d in H_D) (|F_d| - 1)
      + sum_(d in K_D) (|F_d| - 1).

|netForwardHard| + |netReverseStrictRigid| + |unusedCoveredSinks|
 = |singletonCovered| + |softOverlapCovered|
   + |H_D| + |K_D|
   + sum_(d in H_D) (|F_d| - 1)
   + sum_(d in K_D) (|F_d| - 1).
```

Each fibre size satisfies the independently verified
`|F_d| <= Nat.choose n 2`, and distinct members of one fibre
require genuinely distinct unordered colour supports, corresponding
to two-bit 3-colour or four-bit 4-colour difference configurations.
Crucially `|H_D|` can be charged to TRUE holes at most ONCE,
while the additional `|F_d|-1` for any true-hole fibre and all
terms over `K_D` remain separately UNPAID. No fifth-centre
exclusion or support disjointness is presumed.

CI for exact fibre debt:
https://github.com/Charlie-Wang-03/awards/actions/runs/38410685763
PASS 3,254 jobs; both new theorem axiom sets exclude `sorryAx`.
CI for separate covered/uncovered fibre debt:
https://github.com/Charlie-Wang-03/awards/actions/runs/38411627220
PASS 3,256 jobs; all three new theorem axiom sets exclude
`sorryAx`.

Development fixed actual Lean errors: converting the finite
subtype-universe count to the corresponding NET collision Finset
cardinality; unfolding a local `f` alias; parenthesizing the
`(fibre_card - 1)` term INSIDE the sum binder; providing `Fintype`
for a generic complement partition; avoiding expensive uncontrolled
whole-goal rewrites and unbounded elaboration.

**Remaining truthfully OPEN:** exclusion/payment under real planar
`AngleCap` of nontrivial Hamming-2 shared-colour and Hamming-4
disjoint-colour duplicate fibres, cross-inactivity / opposite-bit
fifth-centre covered diagonals, and globally non-reusing terminal
twin, two mixed-rigid debts, soft overlap and projected profile
loss. The sole WIP geometric payment `sorry` is unchanged;
no solution or disproof of full JSP-000404 is asserted.


## Actual original-bridge diagonal injection and bridge-count fibre cap (2026-10-13)

Two new independently sorry-free Lean modules, now imported into the
verified umbrella and the admitted WIP entrypoint:

- `JSP000404Research/ResidualNetCollisionSameBridgeDiagonalInjection.lean`
- `JSP000404Research/ResidualNetCollisionBridgeFibreCapacity.lean`

**Core proof (new nontrivial source-native rigidity):** take TWO genuine
NET hard-transport intersection sink words `w,z`. Each comes with its
UNIQUE original forward and reverse hard source carriers; define its
original soft bridge owner `B(w) = (reverse.lower, forward.upper)`.
Assume `B(w)=B(z)`, and the two source-dependent DOUBLE-FLIP canonical
opposite diagonals coincide. Both sinks lie in the SAME two endpoint
completion cubes. The original forward hard flip colours are retained
active at the reverse lower bridge endpoint; the reverse hard flip
colours are retained active at the forward upper bridge endpoint.
Hence each of the FOUR original flips occurs at a coordinate where
`w` and `z` must agree. But the previously verified EXACT
symmetric-difference identity forces ALL disagreement coordinates
of `w,z` to lie among those colours. Consequently `w=z`.

Lean theorem names:
- `two_flip_same_bridge_equal_target_source_eq`: the fundamental
  source-word rigidity for shared actual two-endpoint completion.
- `net_collision_same_bridge_same_diagonal_source_eq`: same original
  bridge and same canonical target imply same ACTUAL NET source.
- `net_collision_positive_duplicate_requires_distinct_bridges`:
  positive actual canonical duplicate debt forces distinct bridges.
- `net_collision_certified_bridge_owner_mem_two_bit_carriers`:
  each actual original bridge owner belongs to the previously
  proved genuine-source two-bit bridge carrier pool with
  incomparable retained palettes and Hamming disagreement >=2.
- `net_collision_diagonal_bridge_pair_injective`:
  `w |-> (D(w), B(w))` is globally injective.
- `net_collision_fixed_diagonal_fibre_card_le_two_bit_bridges`:
  for ANY target diagonal `d`,
  `|{w in NET | D(w)=d}| <= |twoBitDisagreementBridgeCarriers|`.
- `net_collision_card_le_distinct_diagonals_times_two_bit_bridges`:
  `|NET| <= |D(NET)| * |twoBitDisagreementBridgeCarriers|`.
- `net_collision_duplicate_debt_zero_of_at_most_one_two_bit_bridge`:
  IF the entire genuine filtered bridge carrier pool has size <=1,
  then actual canonical duplicate debt is zero. This is CONDITIONAL
  on the pool bound, NOT an asserted consequence of AngleCap.

The previous global choose-two bound remains valid. Combining both
gives the honest source-fibre cap

```text
|{w in NET | D(w)=d}|
  <= min (Nat.choose n 2)
         (card (twoBitDisagreementBridgeCarriers C exponent)).
```

Importantly, the candidate bridge pool is made of COVERED SOFT
completion faces, not true Boolean holes, and this source-fibre cap
is NOT itself a nonreusing hole payment. Distinct bridges CAN
potentially map to the same canonical diagonal. The NEW proof
removes all SAME-bridge multiple-hit obstruction unconditionally,
leaving specifically the CROSS-bridge diagonal collision problem,
which is now structurally more targeted than the previous
cross-colour-pair obstruction.

CI for the three same-bridge proofs:
https://github.com/Charlie-Wang-03/awards/actions/runs/38415803842
PASS (3,257 jobs); each theorem's `#print axioms` shows
standard kernel axioms only, NO `sorryAx`.
CI for three bridge-owner/fibre proofs:
https://github.com/Charlie-Wang-03/awards/actions/runs/38416260918
PASS (3,258 jobs); NO `sorryAx`.
CI for global multiplicity and conditional debt-zero:
https://github.com/Charlie-Wang-03/awards/actions/runs/38417088862
PASS (3,258 jobs); NO `sorryAx`.

The two observed compiler problems were a dependent/elaboration
mismatch when extracting pair endpoint equalities, resolved using
`Prod.mk.injEq`, and an unsupported linear `omega` proof involving
an opaque natural product, resolved by the honest cases bridge-card
zero or one. No new `sorry`, `axiom`, `admit`, or geometry assumption.

**Still open:** show distinct original NET soft bridges cannot share
a double-flip diagonal under actual planar AngleCap, or charge their
repeated targets to genuinely unreserved global budget without reuse;
also pay covered diagonal/fifth-centre blockers and the
twin/mixed-rigid/soft/projected-loss debts. The unique WIP global
six-source payment `sorry` is NOT closed.


## Exact double-shell bridge filter and four-bit same-role endpoint separation (2026-10-13)

THREE new modules are complete, all entirely `sorryAx`-free, and
imported into `VerifiedOverlapRewire.lean` and the separate admitted
WIP research module:

- `JSP000404Research/ResidualNetCollisionDoubleShellBridge.lean`
- `JSP000404Research/ResidualNetCollisionTargetShellBridgeFibre.lean`
- `JSP000404Research/ResidualNetCollisionFourBitBridgeEndpointSeparation.lean`

Define the ACTIVE-constraint violation set for any Boolean target d
and retained centre u:

```text
E_u(d) = {e in retainedActive(u) | d[e] != retainedBit(u,e)}
```

For each GENUINE net forward/reverse sink collision s, let its
original two hard transport colours be cf, cr; let its unique
original soft bridge owner be (b,v) = (reverse.lower, forward.upper);
and let d be its canonical source-dependent two-flip diagonal.
The kernel has verified the EXACT equalities:

```text
E_b(d) = {cf}     E_v(d) = {cr}
cf in active(b) \ active(v)
cr in active(v) \ active(b)
```

Each violation set is thus a SINGLETON, not merely nonempty. This
is stronger than the earlier assertion d is OUTSIDE both endpoint
completion cubes. It uses actual original hard sources; the reverse
and forward flip colours are proven distinct. No new source assumption
or planar postulate is introduced.

Define the target-DEPENDENT eligible bridge pool B_2(d) by filtering
the certified two-bit / incomparable-palette original-candidate SOFT
bridges (b,v) to those with singleton violation sets E_b(d),E_v(d)
and each violation subset of the corresponding EXCLUSIVE retained
active palette difference.

The checked injection within each original bridge then yields:

```text
for every Boolean target d:
|{s genuine NET collision | certifiedDiagonal(s)=d}|
    <= |B_2(d)|
    <= |twoBitDisagreementBridgeCarriers|.
```

Compared with the earlier target-independent bound, this eliminates
all candidate bridges that do not have EXACT compatible one-bit
endpoint shells for the particular target d. It still counts SOFT
COVERED bridge candidates, never literal true holes.

A strengthened, explicitly CONDITIONAL zero-debt criterion is proved:
IF, for each ACTUALLY HIT diagonal d, `|B_2(d)| <= 1`, then the
entire actual canonical duplicate-image debt E_D is zero. This is
more focused than assuming at most one soft bridge globally, but
is NOT established by the real planar AngleCap hypotheses.

Finally, if two actual NET collisions s,t have the SAME canonical
diagonal target:
- SAME reverse-lower bridge endpoint implies the exact same
  original FORWARD flip colour.
- SAME forward-upper bridge endpoint implies the exact same
  original REVERSE flip colour.
- If their original source Boolean words have Hamming distance FOUR,
  BOTH same-role original bridge endpoints must differ: lower(s)
  != lower(t) AND upper(s) != upper(t).
  This does NOT say all four bridge endpoint vertices are pairwise
  distinct; cross-role coincidences are not excluded here.

The last fact follows since four-bit target duplication is exactly
disjointness of the two original unordered flip-colour pairs, while
any shared SAME-ROLE endpoint would force a common flip colour.

Independent fast Lean certificates:
- https://github.com/Charlie-Wang-03/awards/actions/runs/38422172506
  PASS, 3,259 jobs, TWO new theorems, no `sorryAx`.
- https://github.com/Charlie-Wang-03/awards/actions/runs/38422639723
  PASS, 3,260 jobs, FOUR new theorems, no `sorryAx`.
- https://github.com/Charlie-Wang-03/awards/actions/runs/38423160464
  PASS, 3,261 jobs, THREE new theorems, no `sorryAx`.

A compiler-error pass corrected argument-order polarity in the
existing `flipCompletionWord_off` lemma; no new axioms or admitted
proofs were used. Previous SAME-bridge rigidity and the exact
true-hole vs globally covered duplicate-debt fibre partition stay
unchanged.

**Open nontrivial mathematics:** derive globally valid uniqueness
or genuine non-reused payment for target-eligible TWO-BRIDGE collision
patterns under actual planar AngleCap. The remaining 2-bit motifs
(including same-role shared endpoints), 4-bit same-role-separated
motifs, fifth-centre covered diagonals, source-cross-inactivity,
and terminal twin / two mixed-rigid / soft / projected-loss
debts still need a six-source global payment certificate. The ONE
WIP `sorry` remains intentionally, and no full JSP-000404
solution/disproof is claimed.


## Target-shell exact global duplicate-debt upper bound (2026-10-13)

Following the full independent integration of the exact double-shell
source proof and the target-dependent candidate bridge injection,
`ResidualNetCollisionTargetShellBridgeFibre.lean` contains TWO further
proved, sorry-free theorems:

- `net_collision_duplicate_debt_le_sum_target_double_shell_excess`
- `net_collision_positive_duplicate_forces_two_target_double_shell_bridges`

With `I` the set of genuine NET collisions, `D` its actual certified
diagonal map, and `B_2(d)` the double-shell target-specific compatible
soft bridge candidate pool, Lean proves

```text
E_D = |I| - |D(I)|
    = sum_(d in D(I)) (|D^(-1)(d)| - 1)
   <= sum_(d in D(I)) (|B_2(d)| - 1).
```

If `E_D > 0`, a canonical target d ACTUALLY attained by a NET
collision must exist with `2 <= |B_2(d)|`.

The pointwise bound uses a genuine SOURCE-bridge injection per target.
This global bound uses exact fibre-excess conservation and does not
confuse globally covered target words with TRUE Boolean holes.
It also does NOT prove any target pool has cardinal <= 1 under
planar AngleCap, nor that excess bridge candidates can be paid by
any globally unreserved dyadic profile.

Final *integration* CI:
https://github.com/Charlie-Wang-03/awards/actions/runs/38423845606
PASS, 3,526 jobs including `VerifiedOverlapRewire` and the
separate `PlanarLowerBranchProofAdmittedWIP`. The new two theorem
axiom prints omit `sorryAx`. The sorry audit found exactly ONE
explicit WIP sorry (then line 359), with WIP's admitted theorem
continuing to report `sorryAx`, and no additional admitted axioms.
No complete solution or disproof of JSP-000404 has been obtained.
