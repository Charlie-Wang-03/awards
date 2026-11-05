# Cyclic projection wires and half-integer retiming

Research continuation after `7091e8ca`, 2026-11-05.

This is a proposed all-n proof of threshold family A through a new finite
arrangement argument. Its graph construction, cycle extraction, and retiming
bridge still require complete Lean formalization and further checking. The
reflected-strip return-order lemma and graph rounding algebra are kernel-checked. Family B
remains open, including at the level of the proposed argument. No complete
original-problem theorem follows from the present files.

## The cyclic graph

Let P be a finite set of at least three distinct planar points, with every
angle strictly smaller than pi-lambda, where lambda>0. No three points are
collinear. Choose a generic initial projection direction. As the projection
axis rotates through pi, every pair of projected points exchanges order
exactly once. A triple exchange would give three collinear original points,
so it cannot occur. Disjoint pairs may exchange at the same time and at
different projection heights.

Draw these projection graphs on a strip with angular coordinate theta and
vertical coordinate p dot (cos theta,sin theta). At the two ends, the vertical
coordinates are negatives of each other. Identifying the ends with this
reflection gives an embedded graph on a Mobius strip. Its vertices are the
pairwise crossing events. Each point supplies a closed wire. Its consecutive
crossing events are connected by directed arcs, oriented in increasing theta.
All arcs have strictly positive angular duration, including arcs across the
cut. Two different arcs meet only at crossing vertices.

Normalize theta by lambda, so the original half-period is t=pi/lambda.
An arc e has a wrap number m_e in {0,1}, according as it crosses the chosen
cut. Give it a delay w_e in {0,1}. The delay is one precisely when its two
successive crossings move the chosen point in opposite directions in the
projection order. Across the cut, the movement sign is reversed. For an
internal pair of opposite movements, the angle at the original point equals
pi minus the elapsed angle. Therefore the strict original angle cap gives

    h_v - h_u + m_e*t > 1       if w_e=1,
    h_v - h_u + m_e*t > 0       if w_e=0.

Here h_e denotes an event time in the original cut interval. The same
interpretation applies to the wrap arc by continuing the projection through
another half-period. The total number of sign changes along any complete
wire, with its reflected seam, is odd and positive.

Conversely, nonnegative durations and these unit delays suffice to keep
opposite movements at least one unit apart along a wire. Between any two
opposite movement signs there is an adjacent sign change. Summing the
nonnegative intervening durations retains that unit delay. This observation
will supply the no-monochromatic-two-path condition after retiming.

## Simple cycles have one or two turns around the strip

Take a directed simple cycle of the embedded graph. Its angular coordinate
strictly increases in the covering strip, so its winding r is a positive
integer. Cut at a generic angular coordinate avoiding the finite vertices.
The cycle meets the cut exactly r times. Cutting it there gives r continuous
graph paths, each running once from the left edge to the right edge of a
rectangle.

These paths are pairwise disjoint. An intersection inside the rectangle would
be an intersection of original projection wires, hence a crossing vertex of
the graph. The cycle would then visit that vertex twice. Overlapping wire
segments would likewise repeat a vertex. The cut avoids vertices and the
cycle meets it at distinct points.

Disjoint continuous graph paths preserve their vertical order. If two paths
had opposite endpoint orders, the intermediate value theorem applied to
their difference would force an intersection. Reflection at the seam reverses
the order of endpoints when they are returned to the left side. Thus the
return permutation of the r cut intersections is order reversing.

Every order-reversing permutation of a finite linear order is an involution.
The return permutation is one orbit because the original cycle is connected.
An involution with one orbit has at most two elements. Therefore

    r in {1,2}.

This proof uses the actual embedded consecutive-wire graph. Edges of the
dense triangle-inequality graph may skip intermediate crossings. That dense
graph has a separate embedding obligation, so the winding argument is applied
only to the sparse wire graph.

`MobiusReturnOrder.lean` states the continuous disjoint-path and finite-return
argument with all path hypotheses explicit. Constructing those paths from a
simple projection-graph cycle is an outstanding Lean step.

## An attained half-integer period

For each directed simple cycle C, let W(C) be its integer sum of delays and
r(C) its winding. Define

    T = max_C W(C)/r(C).

There are finitely many simple cycles. A complete wire has positive total
delay, and decomposition into simple cycles shows that T>0. The winding result
puts T in the positive half-integers. Summing the original strict delay
inequalities around every cycle gives T<t.

At period T, set c_e=w_e-m_e*T. Every directed closed walk has sum of c_e at
most zero, because it decomposes into directed simple cycles. Define H(v) to
be the largest c-weight of a directed walk ending at v, allowing the empty
walk and any starting vertex. Removing a nonpositive closed subwalk can only
increase its weight. Hence a maximizing walk may be chosen with no repeated
vertex. The maximum is finite and attained among walks with at most
|V(graph)|-1 arcs.

Appending an arc to a maximizing walk and again removing closed subwalks gives

    H(v)-H(u)+m_e*T >= w_e.

Thus a retiming exists at the exact period T. Each c_e and each H(v) is a
half-integer. Attainment here concerns this finite difference-constraint
system. It supplies a cyclic event schedule, without asserting a new
Euclidean realization of all prescribed directions.

## Retiming retains a valid projection crossing order

There is a direct three-event alternative to the continuation argument below.
It is the preferred formalization target because it makes cut transport
algebraic. Suppose the original order is i<j<k and its crossing order is
A=ij, B=ik, C=jk. Summing consecutive-wire inequalities between these events
and around their complements gives, for the unwrapped terminal times,

    0 <= H(B)-H(A) <= T-1,
    0 <= H(C)-H(B) <= T-1,
    1 <= H(C)-H(A) <= T.

For the two same-movement endpoint pairs, the complementary wire path has a
sign change because of the reflected seam. It therefore has at least one
unit of delay. For the middle point, the internal path has a sign change.
All other constituent delays are nonnegative. The opposite original triangle
orientation gives these inequalities with A and C exchanged.

Write each H(E)-cut as r(E)+q(E)*T, with 0<=r(E)<T and integral q(E).
The displayed span bound shows that the three quotients are either all equal,
or have the patterns (q,q,q+1) or (q,q+1,q+1), in A,B,C order. The relative
order of a pair of points is reversed precisely when its quotient is odd.
Each of these three quotient patterns, with either parity of q, gives a
transitive triangle of pair comparisons. Thus the pair comparison tournament
defines a total order on the whole finite point set.

In the first quotient case, the three residues retain the original order.
In the second case they obey r(C)<=r(A)<=r(B), and in the third they obey
r(B)<=r(C)<=r(A). The same inequalities give all the required gap bounds in
the transported point order. For example, in the second case the new middle
separation is

    r(B)-r(C) = T-(H(C)-H(B)) >= 1.

The other two new gaps are H(B)-H(A) and T-(H(C)-H(A)), both at most T-1.
The first and third cases follow by the same substitutions. Reversing all
three point comparisons leaves these absolute gap statements valid. This
supplies an entirely finite cut-transport proof, once the consecutive-wire
subpath sums are established. The exact checker uses precisely the quotient
parity rule and independently rechecks every resulting triangle.

For completeness, an alternative geometric continuation argument follows.
Interpolate the original event times and period with H and T. For 0<=s<1,
every consecutive-wire duration is strictly positive, since its original
duration is positive and its terminal duration is nonnegative. Consequently
two events sharing a wire never exchange order before s=1. The only changes
in a linear list of crossings are commutations of events on disjoint wires,
and passages of an event through the chosen cut. A disjoint commutation
preserves a valid adjacent-swap list. Passing a crossing through the cut
updates the starting permutation by that adjacent swap.

This gives a finite continuation argument. Event times and the period vary
affinely in s. On a compact interpolation interval, the period stays bounded
away from zero, so only finitely many translates of any event can meet the
cut or another event. Simultaneous independent changes may be ordered
arbitrarily. Shared-wire changes are excluded by strict duration positivity.

Choose the terminal cut off all terminal event phases. Close enough to s=1,
its starting permutation is constant, and the finite crossing list has a
constant refinement of any terminal ties. Its limit is therefore a valid
weak event schedule. Every pair still crosses once in a half-period, and the
unit delay inequalities survive. Initial ordering at this new cut may differ
from the original one and must be transported with the event times.

For an increasing triple i<j<k in this transported order, the crossings ij
and jk move j in opposite directions. Their terminal times must differ by
at least one. Otherwise the corresponding part of j's wire, whose movement
sign changes, would have total duration less than its required unit delay.

Partition the terminal interval [0,T) into ceil(T) half-open intervals of
length at most one. An increasing two-edge path cannot have both event times
in one interval. The existing ordered-edge Boolean coding argument gives

    |P| <= 2^ceil(T).

This argument only needs middle separation. Terminal equalities between other
edge times are permitted by that coding theorem.

## Consequence proposed for family A

For the cardinality step, there is an even shorter alternative that avoids
constructing a transported total order. At an integral target period n, use
the integral edge weights w_e-n*m_e directly in the potential theorem. All
event times can then be chosen integral. Give an event time h the band h mod n
and flip each of its two original endpoint movement signs by the parity of
h div n.

At a fixed point, consider two incident events ordered as in the original
wire. Their unwrapped time difference is between zero and n. If their
original movement signs agree, the difference is at most n-1. If the signs
differ, the difference is at least one. When the two times have the same
residue modulo n, the difference must be zero or n. In the first case their
original signs agree and their quotients agree. In the second case the
original signs differ and their quotients differ by one. Their flipped signs
therefore agree in both cases.

Consequently every point has a well-defined movement sign in every occupied
residue band. Fill unused bands arbitrarily to obtain an n-bit word. For any
two points, their common event has opposite endpoint signs, and the quotient
flip is common to both endpoints. Their words therefore differ in that band.
The words are distinct, giving |P|<=2^n. This proof needs only consecutive-wire
delay sums, modular arithmetic, and binary counting. The full transported
triangle-order construction above remains a separate check of the stronger
retiming interpretation.

For the original strict cap pi-2*pi/(2n+1), take lambda=2*pi/(2n+1), so
t=n+1/2. The cycle argument gives a positive half-integer T<t. Hence T<=n,
and the coding bound yields |P|<=2^n, for every n>=2.

Every step in the written implication above has been exposed so that the
remaining formalization can check the geometry, cyclic lifting, and cut-order
transport separately. The top-level A theorem has not been entered as a
proved Lean declaration. In particular the current return-path theorem alone
does not supply the projection-graph construction or retiming bridge.

For family B, the same method gives T<=n+1/2 from t=n+1. The elementary coding
bound is then 2^(n+1), which falls short of 5*2^(n-2). The outstanding
combinatorial question is the maximum number of wires in a coherent
half-integer schedule. Pairwise row compatibility alone already fails at
twenty-one rows when T=9/2, as recorded in `DIRECTION_ORDER_RESEARCH.md`.

## Reproducible exploratory checks

All statements in this paragraph describe finite executable checks.

- `artifacts/exhaust_order_width.py 7` enumerated 12,349 reflection classes
  of four-point packet models, representing 24,698 triangle orders. It checked
  acyclicity of each event-order graph and half-integrality of each fixed-cut
  optimum with integer difference constraints. This is an exhaustive finite
  observation, with no universal theorem inferred from the enumeration.
- `artifacts/probe_cyclic_wire_width.py` built the sparse cyclic graph for
  599 point/wiring examples. Every optimum was half-integral. Some cyclic
  optima were smaller than their fixed-cut optima. In twenty examples of size
  six through eight, it also enumerated every simple directed cycle and found
  winding one or two.
- `artifacts/check_cyclic_retiming.py` checked 779 exact rational retimings.
  It reconstructed the changed cut order from the parity of each event's
  period shift, checked that this pair relation is a total order, and verified
  every triangle's betweenness, middle separation and endpoint gap bounds.
- The twenty-point obstruction to separate affine maps admits a two-part
  direction retiming at period 18/5. Its parts have ten points each. This
  preserves the distinction between affine realizability and a coherent
  abstract direction schedule.

The new sparse-graph argument arose from these computations. Its general
validity depends on the written embedded-cycle and continuation proofs, and
the final research goal still requires their kernel-checked geometric bridge
as well as a proof of family B.

## Algebraic formalization continuation

`CyclicGraphPotential.lean` now kernel-checks loop erasure from simple-cycle
bounds, the resulting nonpositive closed-walk bound, and existence of an edge
potential in a conditionally complete ordered additive group. Applying it to
integers gives exact discrete event times. Its new results use only the usual
axioms, with no added axioms or admitted declarations.

For the threshold application one can avoid optimizing the period. Given a
strict source period (k+1)/2 and simple-cycle winding r in {1,2}, the integer
cycle delay W satisfies W<r*(k+1)/2. If r=1 then 2W<=k. If r=2 then W<=k,
again giving 2W<=k*r. The simple-cycle bound therefore applies directly to
the integer edge weights 2*w_e-k*m_e. An integer potential yields a doubled
schedule of period k/2. This is the kernel-checked theorem `exists_half_grid_retiming`
in `CyclicHalfGrid.lean`. Family A uses k=2n, and family B uses k=2n+1.

The new return-path and graph-potential lemmas are components of the proposed
global route. The missing actual projection-graph construction, its simple
cycle path extraction, and the algebraic cut-transport connection remain
visible obligations. Family A is still awaiting a complete kernel chain.

## Integral coding continuation after afe0cc61

`IntegralWireCapacity.lean` now kernel-checks the modular sign rule and the
dyadic bound for an integral event system. Its hypotheses give, at every
centre, an absolute incident-time difference at most n, a strict bound below
n when original movement signs agree, and a lower bound of one when they
differ. Every two centres must share an event with opposite signs. These
conditions imply consistent signs in every residue band and distinct n-bit
words. The module also derives integer-time retiming from the half-grid
potential theorem by division by two. The connection from consecutive wire
arcs to these incident-time inequalities remains to be proved.

There are two possible ways to formalize the embedded-cycle bridge.

- Use the original rotating projections and construct each cut cycle path
  as a continuous piecewise projection graph. The checked reflected-strip
  theorem then bounds the number of paths by two. A finite linear dual
  arrangement also works. After a generic rotation, let the dual wire of
  (x_i,y_i) be y_i-s*x_i. Choose M beyond all crossing parameters. The endpoint
  orders at -M and M are reversed, and every path is piecewise affine.
- Derive a finite adjacent-swap reversal sequence from strict triangle
  betweenness. Order all pair events by their original direction, breaking
  disjoint ties arbitrarily. At each cut, the pair comparison obtained by
  flipping the already crossed pairs is transitive. A simple cycle has at
  most one selected route through each crossing event. Its selected tracks
  therefore preserve their order during every adjacent swap. The reflected
  return order again gives an involution with one orbit. This route would
  establish the winding bound directly from a coherent strict direction
  array and could use the existing original-plane direction bridge.

`DirectionCutOrder.lean` now checks that triangle betweenness produces a
strict total cut order, that strict betweenness makes crossing endpoints
adjacent immediately before their event, and that the endpoint orders at
cuts zero and the full width are the original order and its reverse.

For the second route, a shared-wire tie must be excluded. The existing
`rayThetaAt_injective_of_AngleCap` supplies this for actual point sets, and
`genericLocalDirectionValue_eq_cutRotate` relates those parameters to the
generic DirectionData values. The new finite return-network proof has not
yet been implemented. These alternatives describe the outstanding bridge,
without supplying it as an assumed original-problem theorem.

For a finite sweep proof, remove the wrapping arcs from a simple circuit.
The remaining components run from one cut edge to the next in increasing
event order. At each crossing gate, at most one such component uses the
crossing vertex. Any component whose active wire were incident to an unused
crossing would have to pass through that vertex, because wire arcs connect
consecutive events. Thus a gate moves at most one selected component through
two adjacent positions, while the others avoid those positions. Their order
is preserved. At the end, the same wrapping-wire set is met in reverse order.
The induced return has one orbit because the original circuit is one cycle.

One concrete extraction approach tracks the set of selected arcs crossing
each cut between successive events. At a selected crossing, replace its
unique incoming circuit arc by its unique outgoing arc. At every other
crossing this active set is unchanged. Start and end active sets are exactly
the wrapping arcs. Tracking these replacements gives the cut return map.
The two remaining finite obligations are the order preservation of the
active tracks and the one-orbit correspondence with the original circuit.

The upper-strip signed-gap relaxation was also probed without betweenness.
At doubled period five, six centres returned UNSAT. At doubled periods seven
and nine, the first forbidden sizes eleven and twenty-one timed out after
30 and 180 seconds. These SMT observations have no kernel proof and do not
settle the upper-strip relaxation.

An abstract target for the remaining A construction is a `DirectionData V t`
with t<n+1/2 and injective local direction values at every centre. The latter
turns its weak triangle betweenness into strict betweenness. It is available
for actual strict-cap point sets by the projective-ray injectivity bridge.
Sets with at most two points should be handled directly. With at least three
points, each local wire has at least two distinct events, so its closing gap
is constrained by an actual three-point angle.

For a strict source schedule at period n+1/2, the original DirectionData
times of width t can be scaled by (n+1/2)/t. The zero-delay consecutive gaps
are strictly positive by local injectivity. Every one-delay gap is at least
one before scaling and becomes strictly greater than one. Thus this scaling
provides the exact strict edge premise of the checked rounding theorem. It
avoids strengthening the definition of `DirectionData` itself.

For the local integer gap connection, it suffices to prove monotonicity along
each finite wire list and constancy of the sign on every equal-time plateau.
An incident span equal to the entire period forces the two events to be at
the first and last time plateaus. The closing delay then forces their signs
to differ. Integer-valued times supply the unit lower bound for unequal
signs. This is the local-array proof being developed in `CyclicWireLocalGaps`.

That local-array proof has now passed the kernel. `CyclicWireGraph` constructs
the consecutive and closing arrows, proves connectivity using shared events,
and composes retiming with the dyadic code. `OrderedDirectionWires` constructs
the graph from an actual ordered direction array with injective local values,
including opposite shared-event signs and the scaled strict delays. Its
`card_le_two_pow_of_winding` retains one explicit combinatorial premise,
the one-or-two-turn bound for every nonempty simple cycle of this concrete
graph. That premise remains open in Lean.

`ProjectionStrictWireDirections` also checks local-value injectivity for the
generic DirectionData of an actual positive-angle-cap point set, and derives
strict triangle betweenness from local injectivity. The remaining winding
premise is attached to the concrete graph, with the original-plane direction
bridge available for its eventual application.

A possible simplification for the geometric cycle proof starts at any cycle
event and lifts the entire cycle to a continuous graph F on [a,a+r*T], where
r is its winding. The r graphs (-1)^j*F(x+j*T), for 0<=j<r and
a<=x<=a+T, have the cyclic return map `finRotate r`. The cycle endpoint
identity supplies the reflected boundary condition, and simplicity plus
the consecutive-wire embedding supplies their pairwise disjointness. This
avoids a separate first-return decomposition of the wrapping edges.

For family B, the [unit-interval collapse note](UNIT_INTERVAL_RETIMING_RESEARCH.md)
records a new unproved partition statement on coherent half-grid schedules.
It survived 723 exact-schedule tests, including a stronger version fixing
the already active movement bits. Its phase-selection and colouring proofs
remain open.
