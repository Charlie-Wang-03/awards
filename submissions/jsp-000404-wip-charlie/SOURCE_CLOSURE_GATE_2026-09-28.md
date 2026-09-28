# JSP-000404 — Source-Closure Gate

Date: 2026-09-28  
Branch: `research/jsp-000404-sharp-centre`

## Purpose

This gate answers one question only:

> Is there a published, auditable, gap-free proof chain for the canonical all-`N`
> Blumenthal / Erdos-Szekeres / Sendov minimax-angle classification, so that the
> downstream project is reconstructing and formalizing established mathematics
> rather than silently repairing an unproved global step?

No downstream theorem is promoted to a complete solution while this gate is open.

## Frozen target

The target is the actual planar extremal quantity for every admissible cardinality
`N`, with the final Sendov piecewise classification derived from the geometric
extremal definition.

The following do not count as source closure:

- finitely many values of `N`;
- dyadic thresholds only;
- one-sided construction / upper bounds only;
- a surrogate capacity theorem not connected back to the geometric extremal quantity;
- defining `alpha N` directly by the desired closed formula and then unfolding it.

## Gate criteria

The source chain must supply all of the following.

1. **Statement identity.** The source theorem is the same minimax-angle problem,
   not a nearby angle problem.
2. **All-`N` coverage.** Both non-dyadic intervals are covered, not only small or
   dyadic cardinalities.
3. **Geometric-to-capacity bridge.** The proof derives the global dyadic-capacity
   inequality for every feasible perfect generalized configuration from the actual
   geometry.
4. **General-`s` closure.** The arbitrary number of rank-one centres is proved,
   not merely asserted after the `s = 2,3,4` cases.
5. **Final inversion / construction.** The capacity result is connected to the
   final extremal value, with the matching constructions and indexing conventions.
6. **No formula-by-definition shortcut.** The extremal quantity is not replaced by
   the target formula at the definition layer.

## Source A — Sendov, Fundamentalnaya i Prikladnaya Matematika 1(2), 1995

Primary source:

Bl. H. Sendov, *Compulsory configurations of points in the plane*,
Fundam. Prikl. Mat. 1(2) (1995), 491–516.

Authoritative full text:
https://www.mathnet.ru/eng/fpm81

### Rechecked critical passage

The relevant result is Lemma 4.12, pp. 510–512.

The source:

- writes the perfect-configuration weight as
  `|P| = sum_i 2^(k(i))`;
- orders the exponents;
- announces induction on the number `s` of rank-one centres;
- treats `s = 2` and `s = 3` explicitly;
- states the maximizing exponent profiles for `s = 4`;
- then says that if the lemma is proved for `s-1`, the general `s` case has
  two branches, and directly states the maximizing exponent profiles before
  summing the corresponding geometric series.

The displayed general induction step does not contain a derivation from the
induction hypothesis and geometric feasibility constraints to those asserted
maximizing profiles.

### Gate status for Source A

`RUSSIAN_LONG_PAPER_AS_STANDALONE = INSUFFICIENT_FOR_CLOSURE`

This is a proof-source statement, not a claim that the final classification is
false.

## Source B — Sendov, Acta Mathematica Hungarica 69(1–2), 1995, 27–46

Bibliographic identity is verified:

Bl. Sendov, *Minimax of the Angles in a plane configuration of points*,
Acta Math. Hungar. 69 (1995), no. 1–2, 27–46.

An authoritative digitization of the full 1995 volume has been located in the
Hungarian Academy of Sciences REAL-J repository:

https://real-j.mtak.hu/7467/

The repository exposes `ActaMathHung_69.pdf` as a 132 MB volume PDF.

### Current blocker

The full Acta article text has not yet been inspected line-by-line in this gate.
The current retrieval interface rejects the 132 MB PDF as too large to ingest
directly.

Therefore it is not yet known whether the Acta paper:

- supplies the missing arbitrary-`s` derivation;
- repeats the same compressed induction as the Russian long paper;
- or uses a different proof architecture.

### Required Acta audit

Extract pages 27–46 and locate the analogue of the Russian Lemma 4.12.  Record:

1. the exact theorem / lemma numbering;
2. the definition of the extremal quantity;
3. the reduction to perfect generalized configurations;
4. the exact weighted capacity statement;
5. the `s = 2,3,4` cases;
6. every sentence in the arbitrary-`s` induction;
7. the derivation, if any, of the claimed extremal exponent profile;
8. the final passage from the capacity lemma to the all-`N` minimax formula.

Acceptance requires an actual derivation for item 7, or a precise cross-reference
to an earlier proved result that supplies it.

## Secondary check — Jaudon–Parlier

Ghislain Jaudon and Hugo Parlier,
*On angles formed by N points of the Euclidean and Hyperbolic planes*
(2008; arXiv version 2006), explicitly distinguish their maxi-min problem from
Blumenthal's mini-max problem and state that the latter received its full solution
from Sendov, citing the 1995 Acta paper.

This supports the historical attribution of the final result to Sendov, but it
does not independently verify the disputed arbitrary-`s` proof step.

`SECONDARY_HISTORICAL_ATTESTATION = YES`  
`INDEPENDENT_PROOF_CLOSURE = NO`

## Upstream Lean correspondence check

### PR #2804 / Yi-111-a

At pinned commit `f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061`,
`JSP404.alpha` is defined directly by the desired Sendov piecewise formula.
The headline theorem then proves the interval branches by identifying
`Nat.clog 2 N`, unfolding `alpha`, and selecting the relevant branch.

This does not derive the geometric extremal quantity from planar configurations.

`PR_2804_CANONICAL_STATEMENT_CORRESPONDENCE = FAIL`

### PR #2751

The submission text maps JSP-000404 to Erdos Problem #404, whereas the
Blumenthal / Sendov minimax-angle problem tracked by this research branch is
Erdos Problem #504.  Upstream maintainers subsequently closed the PR as partial
progress and requested a complete solution before resubmission.

`PR_2751_CANONICAL_COMPLETE_PROOF = NO`

### PR #300 and other scoped submissions

The scoped formalizations prove genuine portions of the geometric extremal
problem, including small cardinalities, dyadic thresholds, and construction
bounds, but explicitly do not claim the arbitrary-`N` sharp lower-bound
classification.

`SCOPED_UPSTREAM_PROGRESS = REAL_BUT_INCOMPLETE`

## Current gate verdict

```text
SOURCE_CLOSURE_GATE = OPEN
RUSSIAN_1995_GENERAL_S_STEP = NOT CLOSED BY DISPLAYED PROOF
ACTA_1995_SOURCE = LOCATED
ACTA_1995_FULLTEXT_AUDIT = REQUIRED
INDEPENDENT_LATER_COMPLETE_PROOF = NOT YET IDENTIFIED
CANONICAL_COMPLETE_UPSTREAM_LEAN = NOT VERIFIED
```

The only immediate gate-closing task is the Acta pp. 27–46 audit.

## Downstream discipline while the gate is open

The existing research library remains useful and preserved, but no theorem or
README text may describe JSP-000404 as completely proved.

New Lean work should be limited to source-faithful reconstruction or to already
closed lemmas that are unambiguously required by the verified source chain.
Do not launch another open-ended replacement proof route until the Acta source
has been audited.

## Gate outcomes

### PASS

Set `SOURCE_CLOSURE_GATE = PASS` only if the Acta paper or another primary /
independent source supplies a complete derivation of the arbitrary-`s`
capacity step and the remaining all-`N` chain can be mapped lemma-by-lemma.

Then freeze that proof as the canonical natural-language baseline and construct
a source-to-Lean dependency ledger.

### FAIL-OPEN-MATHEMATICS

If the Acta paper repeats the same unsupported general-`s` step and no
independent repair is found, record:

```text
SOURCE_CLOSURE_GATE = FAIL_OPEN_MATHEMATICS
```

At that point any continuation of the current downstream route is explicitly a
new proof-repair research program rather than straightforward formalization of
an established proof.
