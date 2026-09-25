# Sendov 1995, Lemma 4.12 — proof-source audit

## Source

B. Kh. Sendov, *Compulsory configurations of points in the plane*,
Fundamentalnaya i Prikladnaya Matematika 1(2) (1995), 491–516.

Relevant part: §4.3, pp. 510–512 (journal pages), Lemma 4.12.

## Statement used by JSP-000404

For a perfect generalized configuration with rank-one centres
(o_1,dots,o_s), Sendov writes

[
N=|P|=sum_{i=1}^s 2^{k(i)}
]

and, with (u/2=n+delta), claims in the lower branch
(0ledelta<1/2) that

[
|P|le 2^n.
]

The local exponent is

[
k(i)=sum_j igl(lfloor uarphi_{i,j}/2floor-1igr)_+,
]

which is the same floor-excess arithmetic formalized in the present
research branch after setting (t=u/2).

## What the published proof actually establishes explicitly

The paper treats:

- (s=2) explicitly;
- (s=3) explicitly, using the three-centre angle relation (4.24);
- (s=4) by stating the maximizing profiles for the two delta branches.

For general (s), the published proof then says, in substance:

> assume the lemma proved for (s-1); for (s) there are two cases.

For (0ledelta<1/2), it immediately states that the maximum is attained at

[
k(1)=n-1,quad
k(2)=n-2,quad ldots,quad
k(s-1)=k(s)=n-s+1,
]

and sums the corresponding dyadic comb profile to (2^n).

For (1/2ledelta<1), an analogous prescribed profile is stated.

No separate argument is supplied in the displayed induction step showing
that an arbitrary feasible (s)-centre configuration is dominated by this
specific profile.

## Consequence for formalization

The final capacity inequality and the claimed maximizing-profile induction
must be treated as logically distinct.

The research branch has exact-normalization examples with non-comb equality
profiles, including

[
[n-2,n-2,n-2,n-2]
]

and

[
[n-1,n-3,n-3,n-3,n-3],
]

both of which satisfy the Kraft equality

[
sum_i 2^{k_i}=2^n
]

but are not the comb profile printed in the general-(s) induction.

Therefore the proof project must **not** use the published comb profile as an
intermediate theorem unless additional hypotheses are proved that exclude
these profiles.

## Current repair direction

The branch now treats the lower-branch target as a binary Kraft / weighted
partial-code capacity problem.

Active repair interfaces include:

1. `BinaryKraftTree` — arbitrary full binary-tree equality profiles;
2. `WeightedProfileRepair` — total dyadic loss versus total dyadic surplus;
3. `ResidualCompletionAccounting` — exact projected completion mass:
   covered words plus double-covered words;
4. `ResidualLossWords` — exact profile loss as a concrete disjoint word set;
5. `ResidualSliceAccounting` — projected overlaps are exactly the
   intersection of the two residual-bit slice unions;
6. `ResidualUnsafeEdgeBudget` — an unsafe residual edge satisfies
   (k_u+k_v+|J(u,v)|le n);
7. `ResidualUnsafeEdgeOrder` and `ResidualThroughLadder` — the through
   colours consume order room on both sides and force higher-band cross
   diagonals in the standard direction geometry.

The remaining obligation is a genuine global packing / displacement theorem;
it cannot be replaced by the published comb-profile induction sentence.
