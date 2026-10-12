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
