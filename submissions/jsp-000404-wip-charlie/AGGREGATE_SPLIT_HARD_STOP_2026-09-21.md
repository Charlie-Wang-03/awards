# JSP-000404 — Aggregate split existence hard stop

Status: **stable exact-normalized geometric counterexample candidate + exact Lean mass table**.

This note records a simple five-point integer configuration which falsifies the
unconditional claim

> every nonterminal lower-branch fixed-t configuration admits a nontrivial
> binary partition whose two children each at least double their old dyadic
> mass after deleting the opposite child.

The finite mass table is proved exactly in
`JSP000404Research/AggregateSplitExistenceHardStop.lean`.

The Euclidean angle / quotient realization below is numerical with elementary
exact algebra for the maximum-angle witness; it is not yet Lean-kernel
verified.

## 1. Integer realization

```text
P0 = ( 0, 30)
P1 = (-2, -3)
P2 = ( 1,  0)
P3 = ( 0,  0)
P4 = (-3, -3)
```

The maximum-angle witness is `(P0,P3,P1)`.

At `P3` the witness vectors are

```text
P0-P3 = ( 0, 30)
P1-P3 = (-2, -3)
```

so

```text
cos(GA) = -3/sqrt(13).
```

Therefore the supplementary cap angle is exactly

```text
lambda = pi - GA = acos(3/sqrt(13)) = atan(2/3),
t = pi/lambda.
```

High-precision values:

```text
GA     = 146.309932474020213086474505438... degrees
lambda =  33.690067525979786913525494562... degrees
t      = 5.3428209920088361090549770699743297...
n      = 5
delta  = 0.3428209920088361090549770699743297... < 1/2.
```

The next-largest angle is exactly `135°`, leaving more than `11°` of
separation from the maximum witness.

## 2. Root quotient / exponent data

At the same fixed exact-normalization parameter `t`:

```text
P0 : q = [0,0,0,5]   k=4
P1 : q = [1,0,0,2]   k=1
P2 : q = [1,0,1,2]   k=1
P3 : q = [1,0,1,2]   k=1
P4 : q = [1,0,1,2]   k=1
```

Thus

```text
old exponent vector = [4,1,1,1,1]
old dyadic mass      = 16+2+2+2+2 = 24
capacity             = 2^5 = 32.
```

The configuration itself is safely below the desired bound.  What fails is
the proposed universal recursive split mechanism.

## 3. Floor-margin audit

Scaled projective gaps `t*g` are:

```text
P0:
  0.05123764288945
  0.10294515605357
  0.05666810942199
  5.13197008364383

P1:
  1.33570524800221
  0.33570524800221
  0.89705484394643
  2.77435565205798

P2:
  1.09438479508574
  0.24132045291647
  1.39237335742420
  2.61474238658243

P3:
  1.33570524800221
  0.33570524800221
  1.00000000000000
  2.67141049600442

P4:
  1.09438479508574
  0.24132045291647
  1.18152244905919
  2.82559329494744
```

The exact `1` at `P3` is forced by the maximum-angle normalization.  Apart
from that forced equality, the smallest distance to an integer threshold is
about

```text
0.05123764288945.
```

Hence the quotient profile is not a numerical floor-boundary artefact.

## 4. All ten 2+3 partitions fail aggregate doubling

For each canonical partition `A | B`, the table gives

```text
old(A), post(A), old(B), post(B)
```

at the same fixed parent parameter `t`.

```text
{0,1}   | {2,3,4} : 18,32, 6,32
{0,2}   | {1,3,4} : 18,32, 6,28
{0,3}   | {1,2,4} : 18,32, 6,32
{0,4}   | {1,2,3} : 18,32, 6,28

{0,1,2} | {3,4}   : 20,28, 4,32
{0,1,3} | {2,4}   : 20,32, 4,32
{0,1,4} | {2,3}   : 20,24, 4,32
{0,2,3} | {1,4}   : 20,24, 4,32
{0,2,4} | {1,3}   : 20,24, 4,32
{0,3,4} | {1,2}   : 20,32, 4,32
```

The aggregate split requirement is

```text
2*old(A) <= post(A)
and
2*old(B) <= post(B).
```

Every row fails.  The best possible ratio is already

```text
max_split min(post(A)/(2 old(A)), post(B)/(2 old(B))) = 8/9 < 1.
```

The exact finite statement is proved in
`AggregateSplitExistenceHardStop.lean`.

## 5. Perturbation stability

Independent Gaussian perturbations were added to all ten coordinates.  After
each perturbation the actual maximum angle and fixed parameter `t` were
recomputed.

Among samples retaining `n=5` and `delta<1/2`:

```text
coordinate sigma   no aggregate split / eligible

1e-5               300 / 300
1e-4               300 / 300
1e-3               300 / 300
1e-2               300 / 300
5e-2               159 / 220
1e-1                89 / 126
2e-1                25 /  53
```

Up through `sigma=1e-2`, every sample retained the exact best ratio `8/9`.

## 6. Consequence for the proof search

The following increasingly weak unconditional recursive mechanisms are now
rejected:

1. one compensated deletion always exists;
2. a pointwise +1 binary gain split always exists;
3. an aggregate mass-doubling binary split always exists.

The arithmetic modules remain valid **conditional** tools:

- `DeletionThreshold`;
- `BinaryGainSplit`;
- `AggregateBinarySplit`;
- `AggregateSplitTree`.

What is ruled out is an unconditional geometric existence theorem for the
corresponding split at every nonterminal node.

The live global outlets are therefore the direct certificate routes:

- `LabeledBinaryKraftTree.Certificate`;
- `LocalPaletteCertificate` / adaptive ordered-edge colouring;
- or another global invariant that does not require a recursively available
  mass-doubling split.

The small fixed-t terminal program remains useful independently:
`TwoCentreTerminal` is closed, `ThreeCentreTerminal` is now formalized at
the proof-script level, and a direct four-centre terminal is still worth
closing because Sendov's printed proof treats s=2,3,4 separately.
