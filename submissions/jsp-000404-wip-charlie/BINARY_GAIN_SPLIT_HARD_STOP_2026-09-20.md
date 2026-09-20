# JSP-000404 — Binary gain-split hard stop

Status: **stable exact-normalized geometric counterexample + exact Lean arithmetic table**.

This note records a five-centre planar configuration which falsifies the
unconditional recursive claim:

> every lower-branch configuration admits a nontrivial first binary split such
> that every vertex in each non-leaf child gains at least one fixed-t Sendov
> exponent unit.

The conditional arithmetic theorem BinaryGainSplit remains correct. What
fails is the hoped-for geometric existence theorem.

The finite exponent tables are formalized in
JSP000404Research/BalancedBinarySplitHardStop.lean.

The Euclidean angle / quotient realization below is numerical plus elementary
exact algebra; it is not yet Lean-kernel verified.

## 1. Simple integer realization

~~~
P0 = (  0,   0)
P1 = (-12, -12)
P2 = (-14, -11)
P3 = ( -3,  18)
P4 = ( -6,  18)
~~~

The maximum-angle witness is (P1,P0,P3).

At P0 the two witness vectors are

~~~
P1-P0 = (-12,-12)
P3-P0 = ( -3, 18)
~~~

so

~~~
dot = -180
|P1-P0|^2 = 288
|P3-P0|^2 = 333
cos(GA) = -180 / sqrt(288*333)
        = -5 / sqrt(74).
~~~

Hence exactly

~~~
lambda = pi - GA = acos(5/sqrt(74))
t = pi/lambda
  = 3.305037183549897108525007923749232429503669663383...

n = 3
delta = 0.305037183549897108525007923749232429503669663383...
      < 1/2.
~~~

Numerically

~~~
GA = 125.5376777919743826... degrees.
~~~

The next-largest angle is about 118.6949043793 degrees, leaving a gap of about
6.84277 degrees to the maximum witness.

## 2. Full centre quotient / exponent data

At the same fixed exact-normalization parameter t, the five cyclic quotient
profiles are

~~~
P0 : [0,1,0,2]   k=1   support=2
P1 : [0,0,1,1]   k=0   support=2
P2 : [0,0,1,1]   k=0   support=2
P3 : [1,0,0,1]   k=0   support=2
P4 : [1,0,0,1]   k=0   support=2
~~~

Thus the old exponent vector is

~~~
[1,0,0,0,0]
~~~

and the old dyadic weight is

~~~
2 + 1 + 1 + 1 + 1 = 6.
~~~

For the separated support-two source P0, the scaled projective gaps are

~~~
[0.1256423365..., 1.0000000000..., 0.1647492478..., 2.0146455993...]
~~~

so the positive quotient gaps are the separated entries 1 and 2.

The exact unit value is forced by the maximum-angle normalization and is not a
numerical accident.

## 3. Both natural support-two cluster splits fail

The two positive gaps at P0 determine the two ray clusters {P1,P2} and
{P3,P4}.

Assigning P0 to the {P3,P4} side gives

~~~
{P0,P3,P4} | {P1,P2}
~~~

with gains

~~~
P0 : +1
P3 :  0
P4 :  0

P1 : +2
P2 : +2
~~~

Assigning P0 to the other side gives

~~~
{P3,P4} | {P0,P1,P2}
~~~

with gains

~~~
P3 : +2
P4 : +2

P0 : +1
P1 :  0
P2 :  0.
~~~

Hence neither natural cluster split is a pointwise +1 binary gain split.

## 4. All ten 2+3 splits fail

For each two-element side A, the combined child post-exponent vector
(the exponent of every vertex after deleting the opposite child) is:

~~~
A={0,1}: [2,2,2,1,0]
A={0,2}: [2,2,2,0,0]
A={0,3}: [2,0,0,2,2]
A={0,4}: [2,0,0,2,2]
A={1,2}: [2,2,2,0,0]
A={1,3}: [1,2,1,2,1]
A={1,4}: [1,2,1,1,2]
A={2,3}: [1,1,2,2,1]
A={2,4}: [1,1,2,1,2]
A={3,4}: [2,0,1,2,2].
~~~

Against the old vector [1,0,0,0,0], every row contains at least one vertex
whose new exponent is not at least old+1.

Therefore no 2+3 split satisfies the pointwise gain hypothesis.

This finite statement is proved exactly in Lean by
balancedHardStop_every_two_three_split_fails.

## 5. All five singleton+four recursive splits fail too

Allow the singleton side to terminate immediately as a leaf and require only
the four-point survivor child to gain one unit at every remaining vertex.

This also fails for every choice of singleton.

After removing each singleton, the survivor gain patterns are:

~~~
remove P0: P1 0, P2 0, P3 0, P4 0
remove P1: P0 0, P2 +1, P3 0, P4 0
remove P2: P0 0, P1 +1, P3 0, P4 0
remove P3: P0 0, P1 0, P2 0, P4 +1
remove P4: P0 0, P1 0, P2 0, P3 +1.
~~~

Thus no first recursive binary split of a five-vertex configuration has the
form "singleton leaf plus a child in which every survivor gains one".

The exact table is proved in Lean by singletonHardStop_no_gain_child.

## 6. Perturbation stability

Gaussian perturbations were applied independently to the four non-source
coordinates while keeping P0=(0,0) fixed. After every perturbation, the actual
maximum angle and hence exact-normalization parameter t were recomputed.

Among samples which retained the source conditions

~~~
n=3,
delta<1/2,
P0 deficit=2,
P0 support=2,
positive gaps separated,
~~~

the number retaining **no successful 2+3 gain split** was:

~~~
coordinate sigma     retained / eligible

1e-5                 500 / 500
1e-4                 500 / 500
1e-3                 500 / 500
5e-3                 497 / 500
1e-2                 451 / 500
2e-2                 381 / 500
5e-2                 262 / 462
1e-1                 182 / 389
~~~

So the failure is not a floor-boundary artefact.

## 7. Consequence for the proof search

The following increasingly strong conjectures are now rejected:

1. every separated support-two centre yields a successful split by assigning
   the centre to one of its two natural ray clusters;
2. every lower-branch five-centre configuration admits a balanced 2+3
   pointwise +1 binary gain split;
3. every such configuration admits a first recursive split where all vertices
   of every non-leaf child gain one exponent unit.

Accordingly:

- BinaryGainSplit.lean remains a valid conditional arithmetic tool;
- BinarySplitHardStopResolution.lean remains a useful positive example,
  showing some deletion hard stops can be solved by splitting;
- but no unconditional geometric existence theorem for gain splits may be
  assumed.

The live global outlets are therefore the ones which do not require pointwise
gain at every child:

- direct construction of a LabeledBinaryKraftTree.Certificate;
- construction of a LocalPaletteCertificate / adaptive ordered-edge colouring;
- or a weaker weighted split rule which only controls aggregate Kraft mass,
  rather than requiring every survivor to gain one unit.

## 8. Source-normalization warning

Sendov's published Lemma 4.12 assumes

~~~
GA(V) = (1 - 2/u) pi
~~~

for the same perfect generalized configuration V, sets floor(u/2)=n, and then
states that the proof is by induction on the number s of rank-one centres.
The printed general step then directly asserts the maximizing exponent profile.

It does not state an induction theorem for arbitrary child subsets at the
parent's fixed u.

Therefore a binary-split proof must not silently apply Lemma 4.12 to both
children with the parent's fixed normalization unless a separate cap-uniform
theorem is proved. The labelled-Kraft and adaptive-palette routes avoid that
logical issue because they aim to construct a global certificate directly.
