# Narrow observers and weighted direction intervals

Research continuation, 2026-11-05. The arbitrary-N lower bound remains open.
The ordered, coordinate-geometric, and private-direction weighted lemmas passed
Lean 4.34.0 checks. The complete connection from canonical `centreExponent` to
the private-direction family remains to be formalized.

## Interval packing with private directions

Let a finite set of distinct planar centres satisfy the angle cap pi-lambda,
where lambda>0. At centre i, also choose k_i distinct projective directions
whose mutual projective distances, and distances from every line joining i to
another centre, are at least lambda. Suppose every inter-centre direction and
every chosen private direction belongs to the same lifted projective interval
[L,U], with U-L<K*lambda and K a positive integer. Then

    sum_i 2^(k_i) <= 2^K.

Divide [L,L+K*lambda) into K half-open intervals. Orient all edges forward
in this common interval, which has length less than pi in our applications.
Projection on its middle direction gives a strict total order of the centres.
An incoming and an outgoing edge cannot occupy the same interval at a vertex.
Their angle would exceed pi-lambda. Thus each occupied interval fixes a bit at
that vertex, and the interval of any edge fixes opposite bits at its endpoints.
The corresponding Boolean completion sets are pairwise disjoint.

Private directions occupy distinct intervals, each unoccupied by an incident
edge. These statements follow from distance at least lambda and half-open
interval width lambda, including equality at the distance boundary. Hence the
completion set at i has at least 2^(k_i) members, proving the bound.

The usual gap exponent supplies such private directions. In each projective
gap of length g, insert directions lambda,2*lambda,...,k*lambda from its left
endpoint, with k=max(floor(g/lambda)-1,0). Their distance from either endpoint
is at least lambda. Directions selected in adjacent gaps are separated by at
least 2*lambda across their common endpoint. For nonadjacent gaps the same
argument follows along each of the two circular arcs. A single nonempty gap
also leaves a complementary separation of at least 2*lambda. This treats the
cyclic seam. The construction realizes exactly the defining exponent.

## One narrow observer

Suppose z is a centre and all rays from z to the other centres T lie in one
oriented cone [a,a+w] with 0<=w<lambda. The narrow-view argument gives every
inter-centre direction of T a representative in

    [a+lambda, a+w+pi-lambda].

The same interval contains every private direction at a centre x of T.
Indeed its distance from the line zx is at least lambda, so its representative
lies between arg(x-z)+lambda and arg(x-z)+pi-lambda. Thus, whenever

    pi/lambda - 2 + w/lambda < K,

the preceding packing lemma bounds the entire residual weight by 2^K.
This extends the ordinary-point narrow-view bound to the actual dyadic weights.

For t=n+delta, 0<=delta<1/2, a centre of exponent n-1 has all its rays in a
cone of aperture at most delta*lambda. This is the existing sharp-centre
consequence of its single positive gap. The residual interval length is at
most (n-2+2*delta)*lambda<(n-1)*lambda. Its weight is therefore at most
2^(n-1), and adding the sharp centre proves the lower weighted bound 2^n
for every configuration containing a top-exponent centre. This argument leaves
the cases with all exponents at most n-2 open.

## Two narrow observers

Put A=(0,0), B=(d,0), d>0. Let T be a finite set strictly above AB with
all base angles

    a_x=angle(B,A,x), b_x=angle(A,B,x)

strictly smaller than lambda, and suppose all angles of {A,B} union T are at
most pi-lambda. In the applications lambda<pi/2. There is no collinear triple.

For an ordered pair x,y from T, choose its upward projective direction e.
It belongs to both observer intervals. In particular

    a_x+lambda <= e <= pi-b_x-lambda

when y is above x. To justify this ordering, first the broad intervals from
both narrow views confine every inter-centre line strictly between 0 and pi,
so all heights are distinct. The angle cap at x then gives the two displayed
inequalities. Betweenness of the direction of Ay in the directions Ax and xy
gives a_x<=a_y. Applied from B it gives b_x<=b_y. Consequently both base-angle
lists increase in the same height order.

Take r to be the lowest point of T. All inter-centre lines, and all private
directions at all its centres, therefore lie in

    [a_r+lambda, pi-b_r-lambda].

The cap in triangle ABr gives a_r+b_r>=lambda. The common interval has length
at most pi-3*lambda. Hence, if t-3<K, the residual weight is at most 2^K.
For ordinary points set every private-direction set empty.

The use of the same r for both minima is essential. Taking two unrelated
minima and adding them would leave an unjustified extra assumption.

### Consequence for two top exponents in the upper strip

Suppose t=n+delta, n>=3, 1/2<=delta<1, and two centres A,B have exponent n-1.
Every other centre makes base angles at A,B at most delta*lambda<lambda.
They all lie on the same side of AB. Otherwise centres x,y on opposite sides
would give a_x+b_x>=lambda and a_y+b_y>=lambda, whereas sharpness at A and B
would give a_x+a_y<=delta*lambda and b_x+b_y<=delta*lambda. Adding these
inequalities contradicts delta<1.

The two-observer result now applies with K=n-2, since
t-3=n-3+delta<n-2. The total weight is bounded by

    2^(n-1)+2^(n-1)+2^(n-2) = 5*2^(n-2).

This includes the earlier four-centre saturation family. The upper-strip cases
with zero or one top-exponent centre remain open.

## Lean scope

The following are checked in `NarrowObserverDirections.lean`.

- `card_le_two_pow_of_edge_interval` uses only bounded real edge values and
  middle separation. It handles K=0, empty sets, and singleton sets.
- `DirectionData.low_observer_card_le` gives the single-cone cardinality bound
  with its aperture explicitly present in the inequality.
- `DirectionData.two_observer_edge_interval` proves simultaneous monotonicity
  and the common interval of width at most t-3.
- `DirectionData.two_observer_card_le` gives the resulting finite-set bound.

`two_narrow_observer_card_bound` in module `TwoObserverGeometry` and namespace
`JSP000404Research` supplies the actual coordinate-geometric conclusion for a
horizontal base and all selected points strictly above it, with the two strict
base-angle bounds and the original Euclidean angle cap as hypotheses.
`UpperHalfPlaneDirections.lean` constructs its height-ordered angular lift,
including horizontal boundary edges, and derives betweenness from the
parallelogram angle identity. There is no assumed directional realization.

`weighted_capacity_of_private_directions` proves the interval packing bound.
The `DirectionData.PrivateDirections` family records actual finite direction
sets, their ranges, their mutual separation, and their circular separation from
incident lines. Its `low_observer_capacity` and `two_observer_capacity` prove
the weighted residual bounds with those hypotheses. Constructing this family
with cardinalities exactly `centreExponent` remains a Lean obligation.

Their printed transitive axioms are `propext`, `Classical.choice`, `Quot.sound`.
The observer hypotheses remain visible in these statements. No general
cardinality-selection theorem or arbitrary-N result follows from them alone.

The proof uses the existing forward-direction geometry and the classical
Erdos-Szekeres/Hansel bit packing. The new part in this continuation is the
two-observer simultaneous-minimum bound and its weighted high-exponent use.
The single ordinary narrow-view bound was already recorded in
`UNWEIGHTED_AFFINE_THRESHOLD.md` at e2168310.

## Computational continuation and next proof targets

The surviving one-top upper case suggests the following ordered-direction
conjecture. If t=n+delta, 1/2<=delta<1, and a first observer has every outgoing
direction in [0,delta], then at most 3*2^(n-2) residual vertices are possible.
The observer rays increase, each residual edge ij satisfies

    1+a_i <= d_ij <= t-1+a_j,

and strict triangle betweenness still constrains the residual array. The
general statement and its weighted form are unproved.

At delta=99/100, Z3 5.3.3 returned `unsat` for residual sizes 4, 7, 13 at
n=2,3,4. It returned a rational abstract model on 12 residual vertices for
n=4. The n=5, 25-residual query timed out after 180 seconds. These are solver
observations at one delta value. They supply neither a kernel proof nor the
all-delta or all-n claim. The script and JSON results are retained for replay.

A separate numerical search made 561,465 proposals over n=4..7 and both strips,
excluding the newly controlled top-root cases. It found no overweight witness.
Examples meeting the target mass included n=4 upper profile [2,1,2,1,2,2] and
n=4 lower profile [2,0,0,1,2,2]. Coordinates and logs remain under `artifacts/`.
These floating-point runs are search evidence only.

An unrestricted non-losing deletion restricted to convex sets also fails.
For a regular m-gon and m/2<t<2m/3, every centre exponent is zero. Its local
gaps are pi/m and one 2*pi/m gap. Deleting any vertex only creates gaps of
length at most 3*pi/m<2*pi/t, so all surviving exponents are still zero.
Every deletion lowers mass from m to m-1. These configurations are within the
target capacity and leave an overweight-only deletion assertion open.

The separate-affine-map recursion has now been refuted on twenty actual
integer points at t=23/5. Every bipartition has a part whose entire affine
orbit exceeds the child cap at t-1=18/5. The proof uses 296 rational matrix
certificates and exhaustive integer colour checking. Its geometric proof and
exact data are recorded in `AFFINE_PARTITION_OBSTRUCTION.md`; full Lean
geometry remains pending. This also leaves an overweight-only assertion open.

## Affine certificate audit

The e2168310 certificate has the required orbit-wide quantifier. For a fixed
set with at least five points and no collinear triple, every escaping sequence
of determinant-one positive metrics has a largest-eigenvector limit e. Some
triple has three distinct projections along e, so its middle angle matrix has
e-transverse quadratic value strictly positive. Its trace consequently tends
to infinity along that sequence. This supplies compact sublevel sets and an
attained minimum. It does not claim an ordinary minimizing configuration when
the point set itself varies or collides.

At an attained minimizer with positive value c, active-trace balance gives a
positive matrix average C=(c/2)*I in minimizing coordinates. For every other
positive determinant-one metric Q, tr(Q*C)>=c. Thus the local balance is also
a global certificate. Equality forces Q=I, so the minimizing metric is unique
in these coordinates. Positivity is required for this argument. It is present
for the certificate thresholds under consideration. The outstanding task is
still to force the required value of det C at the forbidden cardinality.
