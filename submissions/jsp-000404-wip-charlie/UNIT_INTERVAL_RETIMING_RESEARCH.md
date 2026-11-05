# Unit-interval collapse as a possible upper-strip induction

2026-11-05. This is an unproved research direction for family B. The exact
experiments below supply finite models and colouring witnesses. They do not
prove an arbitrary-size partition theorem.

## Candidate statement

Start with a coherent cyclic crossing schedule of half-period T=n+1/2,
n>=3. Coherence here includes a valid adjacent-swap reversal sequence whose
event times are nondecreasing. Every pair crosses once, and opposite movement
signs at one wire are separated by at least one unit, including the reflected
seam. Equal event times may occur and retain the given crossing refinement.

The candidate says that some cut and some two-colouring of the wires allow
one unit interval to be collapsed in both colour classes. With the cut at
zero, replace each event time theta in [0,T) by max(0,theta-1), and replace
the period by T-1. After retaining just one colour class, the event order
still comes from deleting wires from the reversal sequence. The missing
claim is that both classes retain the unit movement-sign delays.

If this holds, and the coherent period-5/2 base has at most five wires, then
induction would give at most 5*2^(n-2) wires at period n+1/2. Combined with the
proposed half-integer rounding of an original strict cap at period n+1, this
would give family B. The children would be abstract crossing schedules. No
separate Euclidean realization of the collapsed children is required for
this particular cardinality induction.

An unrestricted separate-affine-map step was refuted earlier. That exact
counterexample does admit a common interval collapse after cyclic direction
retiming. These operations have distinct mathematical premises.

The subsequent [nine-wire counterexample](FORCED_INTERVAL_COMPRESSION_COUNTEREXAMPLE.md)
rules out requiring all crossing pairs in the collapsed interval to receive
different colours for every fixed schedule. It has an explicit coherent
refinement and an independent all-phase finite check. The freely coloured
unit-collapse candidate stated above survives that example.

## Exact exploratory tests

`artifacts/probe_common_compression.py` tested the 723 retained exact schedules
with T>=7/2 from the earlier 779-retiming collection. Each period is an
integer or half-integer, and event times come from exact integer graph
potentials. It tests phase cuts on the quarter-unit grid, reconstructs the
parent cut order, collapses the unit interval, and checks every triangle.
Every triangle violating a child gap bound becomes a nonmonochromatic
three-vertex clause. The colouring search uses Z3 5.3.3.0.

All 723 inputs admitted a colouring at a tested phase. Phase zero worked in
721 inputs. It failed in a twelve-wire period-9/2 input, where phase 1/2
worked, and in an eight-wire period-7/2 input, where phase one worked. These
UNSAT outputs motivate allowing the cut to vary. They have not yet been
independently certificate-checked. The original arrays and phase outputs are
retained in `artifacts/common-compression-audit.json` and its input JSON.

The stronger test `artifacts/probe_forced_compression.py` fixes the colour of
every wire active in the collapsed half-open unit interval to its existing
source/sink movement bit. It leaves only inactive wires free. All 723
schedules again had a successful tested phase. The output is retained in
`artifacts/forced-compression-audit.json`.

A further search changed the shortest-path root at the same optimal period.
It found the nine-wire obstruction described above after more than 1,200
successful root schedules. Prescribing the active bits failed at every
phase of that retiming. Independent flips of active components also failed.
The all-phase certificate is checked by the committed standard-library script,
so this strengthened fixed-schedule rule should no longer be pursued.

These runs use a specific exact retiming for each input. They establish
neither the claim for all feasible retimings nor existence of a suitable
retiming for every original configuration. The stronger latter existential
version would still suffice if a universal fixed-schedule statement fails.

There are seven bad triangles with all three wires inactive among the
successful forced-colour phase choices. An argument reducing every remaining
constraint to two-SAT therefore needs an additional selection theorem or a
different structural reduction. The actual counts by number of active
vertices were 7, 32, 658, and 5,110 for zero through three, respectively.

The twenty-point affine obstruction has an exact cyclic optimum 9/2. Its
retimed array admits a collapse at phases 0, 1/4, 1/2, 3/4, and 1, each with
two ten-wire classes. Later sampled phases failed. The script output is in
`artifacts/common-compression-20.json`, with point order reconstructed by the
committed `scripts/check_cyclic_wire_retiming.py` routine.

## Proof obligations and falsification priority

The first task is to seek a coherent half-grid schedule for which every
phase fails, including schedules other than the current canonical graph
potentials. If such a schedule is found, distinguish a failure for that
fixed schedule from failure of the version allowing a prior retiming.

If the conjecture survives, its proof must explain how a phase and freely
chosen colours satisfy all bad-triple clauses. The prescribed active-bit
version has already failed. The one/two-turn cycle theorem and its
original-plane construction are now kernel-checked in the completed family-A
chain at `449be4d2`. The coherent-cut interpretation of a weak retiming would
still need its own formal bridge for this induction.

A further varied-potential search checked 982 distinct schedules and found a
free-colour collapse in every case, discarding 698 duplicates. The output is
`artifacts/free-compression-varied-audit.json`. A separate
[maximal-independent-set encoding](HALF_GRID_INDEPENDENT_SET_RESEARCH.md)
now provides another candidate route to the same B constant.

## Projection-separated independent retimings also fail

Allowing each child its own cyclic time potential still does not make a
straight-line partition sufficient. The retained twenty-point affine witness
has a parent cyclic retiming of width 9/2. Its exact rational projection
sweep yields 190 unordered nontrivial line-separated partitions. In every
partition, at least one child has a negative cycle at width 18/5, and hence
cannot be retimed at width 7/2 either. The selected negative-cycle ratios are
4 in 137 cases and 9/2 in 53 cases.

An unrestricted ten-plus-ten partition of the same points has feasible
independent child retimings at width 18/5. Thus the obstruction concerns
the requirement of a projection separator. The freely coloured collapse
and unrestricted separate-retiming routes remain available.

`scripts/check_projection_partition_retiming.py` verifies the actual sweep,
every negative cycle and the unrestricted positive witness with exact
standard-library arithmetic. The evidence is recorded under
`verification/projection-partition-20261105/`. The earlier 71 ordinary
order tests had all admitted separated partitions, so the sharp twenty-point
input was essential to this falsification.
