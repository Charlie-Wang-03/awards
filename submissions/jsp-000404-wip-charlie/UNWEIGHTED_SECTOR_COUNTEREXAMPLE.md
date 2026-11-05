# A strictly capped planar set with a triangle in every direction interval of width π/n

2026-11-05. This is an ordinary Euclidean counterexample to a proposed
proof of A. It is **not** a counterexample to A. A projective direction
is the direction of a line modulo π. An interval contains a triangle
when it contains the projective directions of all three of its sides.

**Theorem.** For every integer n≥64 there is a set S of 9n(2n+1)
distinct planar points such that:

1. All angles are strictly smaller than π−λ, where λ=2π/(2n+1).
2. Every *open* interval of directions of length w=π/n contains a
   triangle of S.

It follows that no partition of the direction circle into n intervals
can make all n triangle-free: one interval has length at least π/n.
In particular the one-wide-sector route in the earlier proof DAG fails
on actual points. At the endpoint its required width is
π−(n−1)λ=3λ/2>w. Below the endpoint the same implication holds
for n<t<n+1/2 since π−(n−1)π/t>w. Finiteness and the strict
cap allow t sufficiently close to n+1/2 from below. No hypothesis of
being a minimal overweight configuration is tested here.

## Put a small triangle in each required orientation

Let

    M = 3n(2n+1),  h = π/M = (w−λ)/3,  d = λ+h = w−2h.

For each midpoint θ=jh, 0≤j<M, prescribe a separate triangle. With
v(s)=(cos s,sin s), use the three local points

    0,  v(θ−d/2),  v(θ−d/2)+v(θ+d/2).

The two unit sides and their sum have projective directions
θ−d/2, θ+d/2, θ; their maximum interior angle is π−d<π−λ.
Translation and positive scaling leave all three directions exact.
Any interval of width w has midpoint within h/2 of a prescribed θ.
The three directions fit strictly inside the interval, with margin at
least (w−d−h)/2=h/2 at either end. It remains to place all M triangles
so that angles involving different triangles are also capped.

## Place the triangles at separated scales

Use the equilateral triangle with vertices R_i=v(2πi/3), i=0,1,2.
Let T_i be the tangent to its circumcircle at R_i, taken modulo π.
The three T_i are spaced by π/3 on the projective circle, and the two
lines from R_i to the other vertices have directions T_i±π/3.
This follows from the chord direction, perpendicular to the radius at
the midpoint of the corresponding circular arc.

Assign each midpoint θ to the half-open cell [T_i−π/6,T_i+π/6).
Each cell has exactly M/3 grid points since its length is an integer
multiple of h. Use k=floor(n/4) binary levels at each root, with
k directions β_(i,r) equally spaced, including both endpoints, in

    [T_i+3π/8, T_i+5π/8].

There are at least n(2n+1) distinct binary words of length k. Indeed
for 64≤n≤67 even 67·135<2^16, and for n≥64
(n+4)(2n+9)<2n(2n+1); use induction in steps of four. Inject the
midpoints assigned to root i into these words (lexicographic order
will do). No points are needed at unused words.

For the word b assigned to θ, put its three local points q at the actual
coordinates

    R_i + Σ_(r=1)^k ε^r b_r v(β_(i,r)) + ε^(k+1) q,   ε>0.

Representatives of the splitting axes can be chosen once and for all.
For two points from different roots the limiting difference direction is
the oriented root difference. Within a root and between two words, divide
the difference by ε^r at their first differing bit: the limit is
±v(β_(i,r)). Within a word the direction is exactly that of the local
side. Nonzero leading differences ensure distinctness for sufficiently
small ε. These statements describe limits of ordinary coordinates;
no capacity or perfectization assertion is being used.

The following are lower bounds on the projective distance between the
coarse and fine line in any triple that separates at two different
levels. Here d<w≤π/64 and λ<w.

| Coarse and fine line (at the root of the close pair) | Lower bound |
| --- | --- |
| Incident root line and splitting axis | π/24 |
| Incident root line and local side | π/6−d/2 |
| Two distinct splitting levels | π/[4(k−1)] |
| Splitting axis and local side | 5π/24−d/2 |

All four bounds exceed λ: in particular 4(k−1)<n. To check wrap-around,
subtract T_i and take the distance modulo π. The incident lines are
±π/3, the axes range from 3π/8 to 5π/8, and the local sides are within
π/6+d/2 of zero. The table is valid at both ends of each range.

## Check every type of angle

Three points in three different roots have limiting angles 60°. Three
in a single word have the exact prescribed local angles. In every other
triple there is a closer pair: either two share a root and the third
does not, or at their first varying binary level two share the bit and
the third does not. The angle at the outsider tends to zero. At either
point of the closer pair the limiting rays lie on the coarse and fine
lines in one of the four rows above. Either sign of either ray gives an
angle at most π minus their projective distance, hence strictly below
π−λ. The case where all three share an initial sequence of bits is
covered by discarding the common prefix. This exhausts triples.

Here is one **explicit scale** avoiding a limit in the counterexample:

    ε = 1/[100 n(2n+1)].

For a root difference or a first differing bit, divide by its leading
power of ε. The leading vector has norm at least 1. At every lower
binary level the difference of coefficients times unit vectors has
norm at most 2, and the difference of local offsets has norm at most 4.
Thus the norm of the tail is at most 2ε/(1−ε)+4ε ≤ 8ε < 1/2.
All such differences are nonzero, and their ray directions are in
error by at most arctan(8ε/(1−8ε)) ≤ 16ε. A within-word ray has
no error. The four lower bounds in the table are all at least w, so
the mixed limiting angles are at most π−w; the 0° and 60° limits
also satisfy that bound. Perturbing the two rays changes an angle by
at most 32ε < w−λ=π/[n(2n+1)]. Within-word angles already obey the
strict cap exactly. The local directions guaranteeing interval coverage
do not move with ε.

For example n=64 gives 74,304 points at ε=1/825600. The construction
has 3M=9n(2n+1)<2^n
points for n≥64 (check n=64, then the polynomial grows by a factor
less than two per increment). In particular it neither contradicts the
cardinality threshold nor extends the admitted Lean result.
