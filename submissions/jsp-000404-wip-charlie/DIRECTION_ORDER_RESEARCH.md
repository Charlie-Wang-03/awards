# Direction order and joint realization

Continuation after checkpoint `7091e8ca0f0f1e23d7ad3aead1842dd9ad116fab`.
That checkpoint and its parent e2168310 were pushed to the research branch.
Local HEAD, the remote-tracking ref, and the remote branch SHA agreed.
The original all-N result remains open.

## One-observer upper target

The live one-top upper question can be phrased as a real array on an ordered
residual set, with a preceding observer. Write t=n+delta, 1/2<=delta<1. Let
the observer bearings be increasing numbers a_i in [0,delta]. The residual
forward directions obey

    1+a_i <= d_ij <= t-1+a_j,       i<j,

and, for i<j<k, either

    d_ij < d_ik < d_jk,    d_jk-d_ij >=1,

or the reverse strict ordering, with d_ij-d_jk>=1. The remaining two angle
bounds of `DirectionData` follow from the displayed global interval because
delta<1. These conditions are therefore an equivalent strict-direction
reduction of the observer model. The observer's first and last bearings may
be relaxed to 0 and delta, respectively, without excluding any model.

The desired residual bound is 3*2^(n-2). The weighted version is also open.
`artifacts/solve_observer_reduced.py` returned UNSAT for n=3 with seven residual
vertices, and n=4 with thirteen, with delta a symbolic real in [1/2,1).
At n=5 with 25 vertices and delta=99/100 it timed out after 300 seconds.
These solver observations are outside the Lean proof chain.

The a_i can also be eliminated in a weak monotone version. Existence of
nondecreasing a_i in [0,delta] is equivalent to the common edge range
1<=d_ij<=t-1+delta and

    d_jr-d_sk <= t-2     whenever j<r<=s<k.

Necessity follows from the upper bound at r and lower bound at s. For
sufficiency take a_i to be the maximum of zero and d_uv-(t-1) over u<v<=i.
The displayed inequalities put this maximum below every outgoing d_ij-1;
the edge range puts it below delta. Strict observer ordering requires a
separate perturbation argument. This reformulation is written, unformalized.

## Fixed-order width relaxation

Fix the strict triangle-direction orientations of an actual point set or a
reduced adjacent-swap sequence. Minimize a variable t over the associated
linear `DirectionData` inequalities. Replacing strict order inequalities by
weak ones gives the same infimum when a strict realization of the fixed
orientations exists, by convex interpolation with that realization.

The scripts `artifacts/probe_order_type_width.py` and
`artifacts/probe_clustered_order_width.py` tested 599 general point/wiring
instances in 600 trials and 180 clustered, circular, and spiral instances. All returned
optimal widths in half-integers. Half-integrality for arbitrary fixed orders
is an unproved conjecture. A feasible angle array still has a separate
geometric realization obligation. Neither observation supplies a universal
rounding or cardinality theorem.

A possible proof route studies the parametric difference-constraint graph.
Forward same-sign incidence constraints have weight t-1, backward
opposite-sign incidence constraints have weight -1, and order constraints
have weight zero. A cycle gives a rational lower bound on t. To establish
half-integrality one would need a justified reduction of controlling cycles
to ones with one or two t-dependent edges. This reduction is open. Merely
observing half-integral optima supplies no such cycle theorem.

## A 21-row half-grid obstruction with coherent local tests

The preceding relaxation cannot discard the joint direction ordering. The
following explicit family shows the issue even on the exact half-unit grid.
Measure directions modulo 18, with one unit equal to twenty degrees. Use

    A = {1,2,7,8,13,14}
    B = {3,4,9,10,15,16}
    C = {0,5,6,11,12,17}
    S = {1,5,6,7,8,12}.

Take A,B,C, the nine rotations S+2r for 0<=r<9, and the nine arcs
{1+2r,...,8+2r}. These 21 rows all have circular diameter at most seven.
Every pair has an antipodal intersection. Fill the short runs of consecutive
grid points in each row and expand the resulting arcs by epsilon at both
ends, where 0<epsilon<10 degrees. Every three rows separately admit distinct
planar points. Yet the twelve three-arc rows already have no joint realization.
Choosing epsilon<2 degrees keeps each row's diameter below 144 degrees.

Here is a finite proof of the incompatibility. The three cyclic bearings
A->B, B->C, C->A have centres in

    {1,7,13}, {3,9,15}, {5,11,17},

respectively, each with error smaller than epsilon. Of the 27 choices, 18
have a circular gap of at least ten units. They remain contained in an open
semicircle after an error below ten degrees, so three positive-length edges
cannot close. The other nine choices form one orbit under the simultaneous
rotation by two units and the relabelling A->B->C->A.

It suffices to examine the representative (1,3,11). The row S forces S->A
to have bearing five and S->C to have bearing eight, within the same error.
The directed cycle

    S -> A -> B -> C -> S

then has central bearings 5,1,3,17. Every edge has strictly positive
projection on the axis of bearing two, since its central angle differs from
that axis by at most three units, or sixty degrees. Errors below ten degrees
preserve strict positivity. The cycle cannot close. Rotation supplies the
corresponding contradiction for the other eight choices.

The integer checks are in `scripts/check_half_grid_coherence.py`. They also
check that each triple has a choice with largest cyclic gap at most nine. An
arbitrarily small perturbation then makes that gap strictly less than nine,
giving positive lengths that close a nondegenerate triangle. Membership in the
expanded row domains is preserved. This proves the separate-triple assertion.

For every angular cut, the graph of inequalities forced by putting an entire
pair domain inside one open semicircle is acyclic. It suffices to check the
eighteen half-integer cuts. Near an integer cut after expansion, some edges
lose their forced orientation, giving a subgraph of an adjacent checked graph.
The contradiction therefore uses compatible choices across a triangle and
a fourth row. All these conclusions have written proofs with integer checks;
their full Lean geometry is pending.

The earlier fractional 21-row model and its original audit are credited in
`UNWEIGHTED_ROW_CYCLES.md`. This integral family was obtained independently
from maximal signed grid rows. Its 9+12 row pattern follows that same research
motivation. The fixed family supplies a consistency test; arbitrary forbidden
point configurations still require a uniform exclusion theorem.

## Current continuation

The [cyclic-wire continuation](CYCLIC_WIRE_RETIMING.md) now gives a proposed
embedded-graph proof of half-integrality after permitting a change of cut.
It records a written route to all of family A and identifies the geometric
and retiming bridges still awaiting Lean verification. Family B and the
one-observer upper bound remain open. Preserve the actual
direction-realization constraints. The row compatibility or separate-triangle
conditions alone cannot close the main lower-bound problem. The complete
gap-exponent connection for the already proved private-direction capacity
also remains available as a formalization task.
