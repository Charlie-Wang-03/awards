# JSP-000404 — Compensated-deletion numerical hard stop

Status: **numerically stable geometric counterexample candidate + exact Lean arithmetic profile**.

This note records the concrete four-point configuration used to falsify the
over-strong conjecture

> every lower-branch exact-normalized configuration admits at least one
> compensated top-level deletion at the same fixed parameter t.

The exact arithmetic quotient profile is formalized separately in
`JSP000404Research/CompensatedDeletionHardStop.lean`.

The statements in this note concerning Euclidean angles and projective gaps
are **numerical**, not yet Lean-kernel verified.

## 1. Coordinates

The independent random search used NumPy RNG seed `20260920`; the first
candidate found in the reported search was trial 2624.

```text
P0 = ( 0.721283099063816, -0.422510465997642)
P1 = ( 1.889696459431022, -0.839381798736660)
P2 = ( 0.320884653864630,  1.086865290207004)
P3 = (-0.324337662654423, -1.137372705046098)
```

## 1A. Simplified integer-coordinate realization

The same quotient/exponent/deletion pattern survives aggressive rounding.
A particularly convenient realization is

```text
Q0 = ( 7,  -4)
Q1 = (19,  -8)
Q2 = ( 3,  11)
Q3 = (-3, -11)
```

For this integer configuration:

```text
GA  ≈ 126.57303097851934 degrees
t   ≈ 3.369085001390025
n   = 3
delta ≈ 0.369085001390025 < 1/2

original q profiles:
  [1,1,1], [2,0,0], [0,0,2], [0,0,2]

original exponents:
  [0,1,1,1]

original dyadic weight:
  7

all four fixed-t deletion weights:
  6
```

The maximum-angle witness is again `(Q1,Q0,Q3)`.

At `Q0`, the two vectors forming the maximum angle are

```text
Q1-Q0 = (12,-4)
Q3-Q0 = (-10,-7).
```

Hence the supplementary cap angle has cosine

```text
92 / sqrt(160*149) = 23 / sqrt(1490),
```

and may equivalently be described by

```text
lambda_* = atan(31/23)
          ≈ 53.42696902148066 degrees.
```

This simple integer realization is preferred for any future fully formal
geometric counterexample.  It reduces that task to finitely many explicit
inner-product / angle comparisons rather than certification of random decimal
coordinates.

## 2. Exact normalization from the actual maximum angle

Using 80-decimal-digit arithmetic on the decimal coordinates above:

```text
GA = 2.1992031993027842831287939427611435309146626448438 rad
   = 126.005061611717563948773055938... degrees

maximum-angle witness = (P1, P0, P3)

t = pi / (pi - GA)
  = 3.333645807790424443476048297261376581634239866328...

n = 3
delta = 0.333645807790424443476048297261376581634239866328...
      < 1/2
```

The next-largest angle is about `124.4924986478°`, so the maximum-angle
witness is separated by about `1.51256°`.

## 3. Original centre quotient/exponent profile

For every centre, canonical projective ray directions are sorted in
`[0,pi)`, cyclic gaps are normalized by `pi`, and
`q = floor(t * gap)`.

```text
centre P0:
  t*gaps = [1.30563275676913495,
            1.02801305102128949,
            1.00000000000000000]
  q       = [1,1,1]
  k       = 0

centre P1:
  t*gaps = [2.25012303790209612,
            0.57789997329113253,
            0.50562279659719579]
  q       = [2,0,0]
  k       = 1

centre P2:
  t*gaps = [0.57475123621928294,
            0.45011307773015696,
            2.30878149384098454]
  q       = [0,0,2]
  k       = 1

centre P3:
  t*gaps = [0.49437720340280421,
            0.73088152054985201,
            2.10838708383776822]
  q       = [0,0,2]
  k       = 1
```

Hence

```text
(k0,k1,k2,k3) = (0,1,1,1)
W = 2^0 + 2^1 + 2^1 + 2^1 = 7.
```

The exact `t*g=1` entry at `P0` is forced by the maximum-angle
normalization.  It does not contribute to floor excess and therefore does not
affect the dyadic weight.

All other quotient coordinates relevant to the exponent calculation have
substantial distance from their nearest integer; the smallest non-forced
margin in the original configuration is about `0.028013`.

## 4. Every fixed-t deletion has post-weight 6

Delete `P0`:

```text
q profiles = [2,1], [1,2], [1,2]
exponents  = [1,1,1]
post weight = 6
```

Delete `P1`:

```text
q profiles = [1,2], [0,2], [0,2]
exponents  = [1,1,1]
post weight = 6
```

Delete `P2`:

```text
q profiles = [2,1], [2,0], [0,2]
exponents  = [1,1,1]
post weight = 6
```

Delete `P3`:

```text
q profiles = [1,2], [0,2], [0,2]
exponents  = [1,1,1]
post weight = 6
```

Therefore every deletion satisfies

```text
post(r) = 6 < 7 = W.
```

The exact finite arithmetic implication is proved in
`CompensatedDeletionHardStop.lean`.

## 5. Perturbation stability

Around the listed coordinates, independent Gaussian perturbations were tested,
with `t` recomputed from the actual maximum angle after every perturbation.

For each perturbation scale, 500 trials were tested.

```text
coordinate noise sigma   trials retaining
                         n=3, delta<1/2, W=7, all posts=6

1e-6                     500 / 500
1e-5                     500 / 500
1e-4                     500 / 500
1e-3                     500 / 500
5e-3                     500 / 500
1e-2                     494 / 500
```

At `sigma=5e-3`, the observed delta range was approximately

```text
0.26483 <= delta <= 0.42116.
```

Thus the failure of compensated deletion is not a fragile floor-boundary
artifact.

## 6. Consequence

The unconditional induction claim

```text
for every lower-branch exact-normalized configuration,
there exists a top-level centre r such that

  old total dyadic weight <= fixed-t completed post-deletion weight
```

should be treated as **falsified numerically**.

Compensated deletion remains valid as a sufficient branch when its explicit
threshold hypotheses hold; modules such as `DeletionThreshold`,
`RestrictedDeletion`, and `StableDeletionReduction` remain useful.
What is ruled out is using existence of a compensated deletion as the
unconditional final induction step.

The main proof search should therefore prioritize the support-cone /
turn-packing and adaptive even-partition routes.
