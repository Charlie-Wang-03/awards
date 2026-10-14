# JSP-000404 — exact-shell rainbow matching capacity (2026-10-14)

## Historical matching model, corrected by subsequent Lean audit

Prior: any genuine same-target NET collision fibre gives a matching
of the candidate lower-/upper-colour slots. EARLY INCORRECT PREMISE
(now formally refuted): that two distinct candidate edges could
share the same unordered colour support. The verified candidate
soft-shadow injection proves that distinct same-target candidate
edges ALWAYS have different unordered supports.

New: introduce the finite maximum **rainbow matching number**
`targetExactShellRainbowMatchingNumber C exponent d`, defined
by admissible edge sets that are pairwise disjoint in BOTH slots AND
pairwise distinct in their unordered transport flip-colour supports.

Actual same-target source fibre F(d) injects into one such matching,
with EXACT preserved size. Therefore, unconditionally:

```text
|F(d)| <= rainbowMatchingNumber(d) <= ordinaryMatchingNumber(d)
E_D <= SUM_(d in actual image) (rainbowMatchingNumber(d)-1)
mobile hard <= singleton + soft + TRUE boolean holes
               + DISTINCT covered diagonals
               + SUM_(d in actual image) (rainbowMatchingNumber(d)-1)
```

This uses actual distinct-support rigidity, not a fictional
AngleCap-derived matching exclusion. The refined graph still only
contains *candidate source-compatible soft bridges*; its edge count,
matching number, colour capacity, and covered diagonals are NOT
themselves literal Boolean holes or unreserved global surplus.

## Proof audit and open goals

- Source: `JSP000404Research/ResidualNetCollisionRainbowMatchingCapacity.lean`.
- Proof route: canonical colour-support fibre injectivity +
  target-exact lower/upper slot injectivity + exact fibre debt identity.
- All added theorems must pass Lean kernel compilation and
  `#print axioms` without `sorryAx` before being certified.
- The unique WIP six-source geometric payment `sorry` remains.
- NEXT: find a genuinely geometric bound/payment for rainbow
  matching components, keeping fifth-centre, twin, mixed-rigid,
  soft and profile loss debts separate.

Verification: [run 38504690545](https://github.com/Charlie-Wang-03/awards/actions/runs/38504690545) PASS, 3,539 jobs; six rainbow capacity theorems only depend on [propext, Classical.choice, Quot.sound].

## Two-edge rainbow obstruction: equivalent to ordinary matching exclusion

At any genuinely hit diagonal d, it suffices to show:
every candidate-edge pair with DISTINCT lower slots and DISTINCT
upper slots has the SAME unordered pair of flip colours.
CORRECTION: since distinct eligible candidate edges are always
colour-distinct, the hypothesis also excludes all two-edge ordinary
matchings. It is NOT a weaker exclusion for the actual graph.

`ResidualNetCollisionRainbowPairObstruction.lean` certifies:
- all rainbow matching sets are of size ≤1 under this condition;
- the finite rainbow matching number ≤1;
- global actual NET canonical duplicate debt = 0 if the condition
  holds at all actually hit d;
- the literal-hole + distinct-covered-diagonal mobile inequality
  without a duplicate-debt term;
- conversely, positive duplicate debt implies an actual hit target
  graph contains two edges with **disjoint lower slots**, **disjoint
  upper slots** and **DIFFERENT original unordered colour pairs**.

The assumption that all disjoint candidate edge pairs clash in
colour support is still an EXTRA unproved geometry hypothesis:
no AngleCap consequence has been asserted.

Verification: [run 38504957833](https://github.com/Charlie-Wang-03/awards/actions/runs/38504957833) PASS, 3,540 jobs; five rainbow two-edge obstruction theorems only depend on [propext, Classical.choice, Quot.sound]. Both runs compiled the verified umbrella and WIP module; the latter retains the historical sole sorryAx.

## Candidate graph: four original endpoints separated by disjoint colours

The module `ResidualNetCollisionCandidateColourVertexSeparation.lean`
uses the **exact cardinality-one violation shells** already required
for each candidate bridge. For any TWO candidate eligible edges of
the SAME target d, even if neither is known to come from an actual
NET source, DISJOINT unordered flip-colour supports imply all FOUR
cross-edge source bridge endpoints are distinct (lower/lower,
upper/upper, lower/upper and upper/lower).

Conversely, sharing a vertex in ANY endpoint role forces the
candidate edges' original two-colour supports to intersect.

This lifts previously proved four-bit source-only rigidity to the
ENTIRE source-compatible target candidate graph. It narrows the
remaining source-compatible motifs, but does not assert AngleCap
exclusion, global Boolean hole payment, or a lower bound on any
unreserved profile surplus. Lean CI [38506236757](https://github.com/Charlie-Wang-03/awards/actions/runs/38506236757) PASS, 3,541 jobs, two new theorems sorry-free (only standard Lean axioms).

## Every candidate edge has a covered common shadow completion

The new `ResidualNetCollisionCandidateShadowCompletion.lean`
certifies a **new stronger bridge-witness law** from the exact
target shells themselves. For each candidate graph edge
e=((b,cr),(v,cf)) at target d, define the reverse two-flip
shadow s_e := flip(cf, flip(cr,d)). Then Lean proves

- s_e lies in BOTH original bridge retained completion cubes
  (at b and at v).
- Consequently s_e lies in the full union of COVERED completion
  words, so it is definitively NOT a TRUE Boolean hole.

This result is about ALL geometrically eligible candidate edges,
not just real NET source collisions. It does not certify that
the edge has a hard-source provenance or that distinct edges
have distinct shadow words, and the shadow is a covered resource
rather than an unreserved global payment credit.

The bridge between graph incidence and Boolean completion cubes
is materially strengthened; geometric matching exclusion and
six-class global payment remain OPEN. Lean CI [38506654774](https://github.com/Charlie-Wang-03/awards/actions/runs/38506654774) PASS, 3,542 jobs, three new theorems sorry-free.

## Fixed-target candidate edge -> REAL soft word injection

`ResidualNetCollisionCandidateShadowInjection.lean` strengthens
the candidate-shadow relation. The chosen bridge is proved an
oriented soft-overlap carrier. The two-flip word is therefore
genuinely in `softOverlapCompletionWords`, not just in the
larger covered-word union. Because every retained completion word
has at most two vertex owners, the original bridge pair is UNIQUE.

For a FIXED diagonal target d, the two singleton violated active
colour sets then determine both original colours. Hence equal
two-flip shadow words force equal candidate edges. This gives
a source-provenance-free injection:

  candidateEdges(d) -> ACTUAL softOverlapCompletionWords,

and consequently `|candidateEdges(d)| <= |softOverlapWords|`.

The map is NOT established globally injective across distinct
targets d; neither soft word capacity nor this inequality is a
TRUE Boolean hole or an unreserved dyadic credit. A correct
global source-payment argument must still allocate these already
covered witnesses without reusing them.

CI: initial run [38506989335](https://github.com/Charlie-Wang-03/awards/actions/runs/38506989335) FAILED due to one **Lean proof projection typo** in the upper-endpoint reverse-colour proof (`heData.2.2.1` erroneously selected forward-colour violation membership, should be `heData.2.1`). This did not expose a mathematical counterexample. Fixed by commit `a72b126a`.

Final run [38507215558](https://github.com/Charlie-Wang-03/awards/actions/runs/38507215558) PASS, 3,543 jobs. All four theorems in `ResidualNetCollisionCandidateShadowInjection.lean` print only the standard axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; verified umbrella and admitted WIP entry both build. The only `sorryAx` is the prior, explicitly admitted global six-source geometric payment.

## CRITICAL AUDIT: Rainbow matching does NOT sharpen this graph

The previously certified per-target candidate-edge-to-soft-shadow
INJECTION has a mathematical consequence overlooked when the rainbow
matching number was first introduced:

- At fixed d, two flips at the same UNORDERED pair of colours produce
  exactly the same shadow completion word.
- That shadow determines a unique actual SOFT bridge owner, and
  the singleton retained-active violation sets determine both slots.
- Thus every candidate edge at d has a UNIQUE unordered flip-colour
  pair, even if it does not come from an ACTUAL NET hard-source pair.
- Consequently every ORDINARY matching is already RAINBOW and
  **rho(G_d) = nu(G_d)**. A purported improvement via rainbow
  matching was overclaimed and must not be used as a strict
  reduction of the eligible candidate graph.

The new `ResidualNetCollisionRainbowRedundancyAudit.lean`
formalizes this equality and the underlying injectivity. The earlier
conditional two-edge colour-clash hypothesis on the ACTUAL eligible
graph in fact implies the absence of ANY two distinct slot-disjoint
candidate edges; it does not leave additional ordinary matchings
in this exact-shell graph.

This correction does not invalidate prior verified inequalities:
they remain TRUE but some are equalities / rephrasings instead of
strict improvements. The only meaningful further tightening must
come from genuinely NEW geometry or global non-reused payment, not
renaming this candidate matching's colour constraint.

Axiom and CI proof for these audit claims pending.

## Target-local Hamming-two SOFT sphere refinement

Candidate graph edge e of fixed d maps INJECTIVELY to a genuine
covered SOFT shadow word s_e. The pair of original transport colours
has two DISTINCT coordinates and s_e differs from d at EXACTLY those
two coordinates. Thus the image is not all global soft words but
the ACTUAL target-local Hamming-two soft sphere:

  S2_soft(d) = {s in softOverlapCompletionWords(C) :
                 Hamming(s,d) = 2}.
  |actual NET fibre(d)| <= |candidateEdges(d)| <= |S2_soft(d)|
                              <= |all soft words|.

The exact duplicate-debt sum inherits the target-wise
sum(|S2_soft(d)| - 1) upper bound. Unlike the earlier (vacuous)
rainbow-vs-ordinary matching distinction, S2_soft(d) can genuinely
exclude irrelevant soft words from the bound. Its cardinal still
counts COVERED words, NOT true holes or a non-reused surplus budget;
a global cross-target payment remains open.

Source: `ResidualNetCollisionLocalSoftSphereCapacity.lean`.
First 7 theorems verified in [run 38512146479](https://github.com/Charlie-Wang-03/awards/actions/runs/38512146479), 3,545 jobs PASS, no `sorryAx`. The new MIN-combined bounds, their debt and mobile ledger, and the conditional local-sphere uniqueness exclusion await the next build.

## Corrected sharpest certified necessary capacity gate

Let `L2(d)` count actual COVERED SOFT words at Hamming
distance exactly two from diagonal d, and `nu(d)` be the ordinary
exact-shell candidate matching number. The proof establishes

  |F_d| <= nu(d) <= |candidateEdges(d)| <= L2(d).

Hence `min(nu(d), L2(d)) = nu(d)` ALWAYS: an attempted apparent
strengthening via a minimum is in fact redundant. Likewise, the
min-based duplicate-debt excess sum equals the old matching-number
excess sum. Keep the local Hamming-two structure certificate, but
do NOT credit this reformulation as an independent capacity gain.

NONE of `L2(d)`, `nu(d)`, `rho(d)` provides automatic TRUE
Boolean hole credit or unreserved profile surplus. The remaining
hard step is geometric/ledger-level global payment for all six
independent debt families. Validation pending.

## Final bound redundancy verification (2026-10-14)

Three no-sorry theorems in `ResidualNetCollisionLocalSoftSphereCapacity.lean`
prove `nu(d) <= L2(d)`, `min(nu(d),L2(d))=nu(d)` and equality
of all hit-target duplicate-debt excess sums. The exact-shell
colour-support rainbow number was previously also proved equal
to the ordinary matching number.

These are valuable AUDIT results: correct earlier capacity upper
bounds have not independently shortened the unique global geometric
payment `sorry`. Next mathematics must produce new AngleCap
restrictions or globally distinct hole/surplus resources.
Lean CI and axiom audit pending.

## Actual low-colour NET debt elimination (NEW restricted theorem)

`ResidualNetCollisionLowColourNoDuplicate.lean` formalizes the
quantitative consequence of the already certified real-source
colour pair injection for small n:

- n <= 1: no genuine NET forward/reverse hard sink collisions
  (already proved elsewhere in the repository; NOT a new lemma).
- n <= 2: every ACTUAL target diagonal fibre has at most ONE source.
- Thus the canonical NET diagonal map is **GLOBALLY INJECTIVE** and
  the real duplicate-image debt is **ZERO**, with no extra geometry
  hypothesis beyond the usual one-layer residual budget.
- The exact NET mobile hard ledger now contains TRUE holes plus
  distinct COVERED target blockers but no duplicate debt, for n<=2.

This is a genuine partial closure of ONE six-source debt
in the small-colour regime, not proof of the planar dyadic
inequality even for n<=2. The full-root and fifth-centre gates
remain open. Lean CI pending.

Lean CI first run [38514847387](https://github.com/Charlie-Wang-03/awards/actions/runs/38514847387):
FAILED on a duplicate **pre-existing** theorem name for n<=1 and
an incomplete application of `Finset.card_le_one`. Both are Lean
engineering errors, not counterexamples. The first theorem has been
deleted as redundant; `card_le_one` is now applied to both elements
and their memberships. Revalidation pending.
