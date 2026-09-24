# JSP-000404 — Sendov Lemma 4.12 source audit

Date: 2026-09-24  
Branch: `research/jsp-000404-sharp-centre`

## Source

Bl. H. Sendov, *Compulsory configurations of points in the plane*,
Fundamentalnaya i Prikladnaya Matematika 1:2 (1995), 491–516.

Math-Net record: https://www.mathnet.ru/eng/fpm81  
Full-text PDF: https://www.mathnet.ru/links/eef0db734420f09dc5b12747cc56dff5/fpm81.pdf

The relevant proof is Lemma 4.12 near pp. 510–512 of the printed paper.

## What the source actually does

For the lower branch it introduces the weighted quantity

[
N=sum_{i=1}^{s} 2^{k(i)}
]

and orders the centre exponents before proceeding by the number (s) of
centres.

The source explicitly treats the small cases (s=2,3,4).  For the general
case it then invokes induction on (s) and states an extremal exponent profile
of comb form, after which the desired dyadic estimate is obtained by summing a
geometric series.

The displayed passage does not provide, in that location, a derivation from
the geometric hypotheses to the asserted general extremal profile.  Therefore
the current formalization does **not** import that profile as an axiom or as a
proved optimization theorem.

This is a proof-gap audit of the exposition used by this project.  It is not a
claim that the final Blumenthal/Sendov theorem is false.

## Why the project does not use the comb profile as a replacement lemma

Exact-normalization exploration and the formal Kraft layer show that the sharp
dyadic capacity has non-comb equality profiles.  Examples at the arithmetic
Kraft level include

- ([2,2,2,2]), the balanced four-leaf tree;
- ([1,3,3,3,3]), one depth-one leaf plus four depth-three leaves.

Corresponding exponent profiles may saturate

[
sum_i 2^{k_i}=2^n
]

without having Sendov's displayed comb pattern.  Thus a correct repair should
target the dyadic capacity itself, not uniqueness of a sorted extremal
profile.

Lean modules:

- `JSP000404Research/BinaryKraftTree.lean`
- `JSP000404Research/AlternativeKraftExtremizer.lean`

## Correct induction interface extracted from the source strategy

The small cases are already handled independently in this branch.  To repair
the induction it is enough to prove the following strictly weaker
minimal-counterexample statement.

For every finite subconfiguration (S) with (|S|ge5), if

[
W(S):=sum_{vin S}2^{k_S(v)} > 2^n,
]

then there exists (rin S) such that, at the same fixed Sendov parameter,

[
W(S)le W(Ssetminus{r}).
]

Indeed, a minimal-cardinality overweight counterexample would then admit a
smaller overweight counterexample, contradiction.

This does **not** require every safe configuration to possess a compensated
deletion.  Exact-normalization searches have produced safe configurations for
which every deletion lowers total dyadic mass, so the unconditional statement
is known to be too strong.

Lean module:

- `JSP000404Research/OverweightDeletionInduction.lean`

The main abstract theorem is
`restricted_capacity_of_overweight_deletion`.

## Current formal target

The remaining geometric/combinatorial obligation can therefore be stated
cleanly:

> **Overweight deletion existence.**  
> In the lower branch (delta<1/2), for an actual planar Sendov
> configuration with at least five centres, if its fixed-(t) dyadic mass is
> (>2^n), then some vertex deletion is compensated.

Existing local tools relevant to this target include:

- exact binary floor carry and merge-gain classification;
- zero-gain rigidity;
- arbitrary-length cyclic first-ray deletion arithmetic;
- support-one global transition-arc packing;
- support-two stable/separated-positive structure;
- top and second-layer multiplicity around a sharp centre;
- weighted deletion averaging and the sharp total-bonus threshold;
- reduction from compensated deletion to controlling the total weight of
  stable centres.

No current Lean theorem claims this final existence statement.

## Fail-closed rule

Future work must not replace the missing step by any of the following
previously falsified strengthenings:

- unique comb extremizer / comb tail majorization;
- unconditional compensated deletion;
- universal pointwise (+1) deletion gain;
- universal aggregate split;
- top-centre deletion doubling;
- hard-residual-pair deletion gain in either fixed direction.

Any proposed strengthening should first be subjected to exact-normalization
counterexample search before being promoted to a formal target.
