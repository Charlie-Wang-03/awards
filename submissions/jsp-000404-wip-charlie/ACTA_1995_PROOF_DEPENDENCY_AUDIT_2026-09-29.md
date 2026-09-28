# JSP-000404 — Acta 1995 proof-dependency audit

Date: 2026-09-29
Branch: `research/jsp-000404-sharp-centre`

Primary source: Bl. Sendov, *Minimax of the Angles in a Plane Configuration
of Points*, Acta Math. Hungar. 69 (1995), 27–46. The digitized article is
physical PDF pages 29–48.

## Dependency chain

```
Def. 2.8 alpha(N), G_alpha(N)
 -> Thm. 2.1 G_alpha(N)=alpha(N)
 -> Lemmas 3.1–3.8 perfectization/local dyadic exponents
 -> Thm. 3.1 perfect-GC reduction
 -> Lemma 4.1 global dyadic capacity
 -> Lemma 4.2 upper bound for N(a)
 +  Lemma 4.3 constructions
 -> Thm. 4.1 all-N formula

Section 5 / Thm. 5.1: attainment by extreme GC's
```

## A. Canonical target and generalized configurations

Definition 2.8 genuinely defines the geometric extremal quantity rather than
the desired formula. Theorem 2.1 gives the ordinary/generalized equivalence by
h-normal approximation.

Verdict: `SOURCE-CLOSED ENOUGH`.

The downstream branch has not yet assembled a canonical final `alpha(N)`
theorem, but this is not the active hard gap.

## B. Perfectization

Lemma 3.8 states that every GC V has a perfect V* with

```
|P*| >= |P|,   GA(V*) = GA(V).
```

Theorem 3.1 immediately strengthens this to an infimum over perfect GC's with
`|P| = N`. The exact-cardinality strengthening is not derived by an explicit
trimming/refinement lemma.

Verdict:
`LEMMA_3_8 = usable`
`THEOREM_3_1_EXACT_N = repairable or bypassable`.

The downstream direct planar-capacity route can bypass perfect GC machinery.

## C. Source local exponent and downstream correspondence

Sendov's local exponent has the form

```
k(i) = sum_j (floor(u * phi(i,j) / 2) - 1)_+.
```

With `t=u/2`, this matches the downstream floor-excess object built in:

- `CentreProjectiveCycle.lean`
- `CentreQuotientData.lean`
- `CentreExponent.lean`

Verdict: local source-to-Lean arithmetic is represented.

## D. Lemma 4.1 small-s cases

For `u/2=n+delta`, the lower branch target is

```
sum_i 2^(k(i)) <= 2^n,    0 <= delta < 1/2.
```

Source:
- s=2: explicit;
- s=3: explicit case analysis;
- s=4: the text merely says the maximum is achieved at a printed profile.

Downstream lower-branch repairs:

- `TwoCentreTerminal.lean`
- `ThreeCentreTerminal.lean`
- `FourCentreCapacity.lean`

Thus lower s<=4 is independently closed downstream even though the source
s=4 optimization is omitted.

## E. Lemma 4.1 arbitrary-s step

After s=4 the Acta text says, in substance:

```
Assume the lemma for s-1. For s there are two cases.
```

It then immediately prints the maximizing exponent profiles and sums their
geometric series. No deletion, merge, majorization, or other derivation from
the induction hypothesis to those profiles is displayed.

Verdict: `DEEP-OPEN`.

The printed comb profile cannot be used as a formal lemma: the downstream
Kraft layer has non-comb equality profiles.

The correct downstream induction shell is already formalized in:

- `CompensatedDeletion.lean`
- `OverweightDeletionInduction.lean`

The remaining lower-branch premise is the geometric existence statement:
every overweight configuration with at least five centres must admit a
fixed-t non-losing deletion, or an equivalent global capacity certificate.

Current status:

```
ABSTRACT_INDUCTION = CLOSED
LOWER_SMALL_CASES = CLOSED
LOWER_GENERAL_GEOMETRIC_CAPACITY = OPEN
```

The current six-point Hamiltonian-residual work is only one terminal analysis
inside this open node.

## F. Upper delta branch

The source's second branch is

```
1/2 <= delta < 1,
sum_i 2^(k(i)) <= 2^n + 2^(n-2).
```

The same unsupported arbitrary-s jump is used.

The current downstream library is primarily lower-branch
(`delta < 1/2`) work. No general arbitrary-cardinality theorem currently
replaces the upper branch.

Verdict:
`SOURCE_GENERAL_UPPER = DEEP-OPEN`
`DOWNSTREAM_GENERAL_UPPER = OPEN`.

## G. Lemmas 4.2 and 4.3

Lemma 4.2 transfers the capacity estimate to `N(a)). This needs an explicit
bridge from `GA(V) <= a` to the fixed-parameter capacity theorem and
monotonicity in the parameter.

Verdict: `REPAIRABLE-ASSEMBLY`.

Lemma 4.3 gives explicit two-centre / three-centre constructions for the two
thresholds.

Verdict: `SOURCE-CLOSED IN OUTLINE; LEAN REALIZATION STILL NEEDED`.

## H. Final inversion defect

Immediately before Theorem 4.1 the paper states
`alpha(N(a)) = a`.

As a blanket statement for real a this cannot be correct: `N(a)` is
integer-valued and stepwise while a varies continuously.

Concrete source-internal example: take n=3 and any 6<u<7. Lemmas 4.2–4.3 give
`N((1-2/u)pi)=8`, while the introduction records `alpha(8)=2pi/3`.
These are unequal unless u=6.

The correct formal interface is a generalized-inverse relation such as

```
N <= N(a)  <->  alpha(N) <= a
```

with attainment, or an epsilon version without attainment.

Verdict: `REPAIRABLE-ASSEMBLY`, not a new geometric obstacle.

## I. Section 5 attainment

Theorem 5.1 supplies extreme GC's by compactness and recursive blow-up.

Verdict: source argument exists but is expensive to formalize. A direct proof
of the two inequalities for the canonical infimum can bypass this section.

## Source-to-Lean ledger

| Dependency | Source | Downstream |
|---|---|---|
| canonical alpha | usable | final assembly absent |
| local exponent | usable | represented |
| s=2 lower | closed | closed |
| s=3 lower | closed | closed |
| s=4 lower | omitted optimization | independently closed |
| arbitrary-s lower | missing | active repair, open |
| arbitrary-s upper | missing | open |
| constructions | outlined | not finally assembled |
| inversion | defective as written | must replace |
| all-N theorem | depends on above | absent |

## Critical path

`CP-1`: prove the lower-branch global capacity

```
sum_i 2^(centreExponent_i(t)) <= 2^n
```

for every finite planar configuration under the fixed angle cap and
`0 <= delta < 1/2`.

`CP-2`: prove the upper-branch global capacity

```
sum_i 2^(centreExponent_i(t)) <= 2^n + 2^(n-2)
```

for `1/2 <= delta < 1`.

After CP-1 and CP-2, the remaining defects are mainly theorem assembly,
construction formalization, and correct threshold inversion.

## Verdict

```
ACTA_1995_FULLTEXT_AUDIT = COMPLETE
ACTA_1995_AS_GAP_FREE_BASELINE = FAIL
GENERAL_S_LOWER_CAPACITY = DEEP_OPEN
GENERAL_S_UPPER_CAPACITY = DEEP_OPEN
FINAL_INVERSION = REPAIRABLE
SOURCE_CLOSURE_GATE = OPEN_EXTERNAL_SOURCE_OR_PROOF_REPAIR
```

Any continuation should be described as `proof repair + formalization`, not
line-by-line formalization of a closed published proof.
