# Five projection cycles in the fixed 21-row model

2026-11-05. **At most 17 of these particular 21 rows can be realized
simultaneously by distinct planar points.** This is an upper bound for
one set of prescribed row domains, not a bound of 17 for arbitrary
144-degree point sets. In particular it does not prove B at n=4.

Input and credit: the 21 rows, their pairwise antipodal compatibility
and the earlier three-row obstruction on rows 7,9,10 come from
[jerrylijize1224-star's snapshot](https://github.com/jerrylijize1224-star/jsp404-lean-partial/tree/09b2ee9cab2da6ca977f682f1c8359b5e90d13d0).
Use its zero-based indexing and angular period 18 (one unit is π/9).
The [earlier checker](scripts/check_public_arc_obstruction.py) verifies
the archive digest, all row diameters, all 210 pair conditions and that
three-row obstruction. The following is a separate deduction from the
row intervals, not a new numerical value for the original problem.

**Increasing-cycle test.** Let D_ij be the allowed oriented bearings
from i to j: intersect row i with row j translated by the half-period.
If, on a directed cycle, every option on every edge lies in the same
open semicircle (a,a+9) modulo 18, the cycle has no realization.
Projection on the axis at angle (a+9/2)π/9 would strictly increase
along every edge. Equivalently the sum of the edge vectors could not
be zero. This uses positive edge lengths; a cycle of coincident
placeholders is not a realization.

Here each entry means the cycle closes from its last index back to its
first. The listed a puts the *whole* permitted intervals inside the
open semicircle, including their endpoints and all wrap-around pieces.

| Cycle | a |
| --- | --- |
| 3,15,17 | 3 |
| 7,9,10 | 53/7 |
| 7,12,16 | 19/2 |
| 9,12,20 | 2 |
| 1,11,19,13 | 7 |

For example, the four directed edges of the last cycle must have bearings
in [143/15,287/30], [106/15,77/10], [34/3,121/10],
[44/3,153/10], respectively. All four fit strictly between 7 and 16.
This obstruction does not contain the old bad triangle. In fact **every
three of these four rows are individually realizable**. Each row below
lists a simultaneous choice of the three cyclically directed bearings
i→j, j→k, k→i; the choices need not agree between different triples.

| i,j,k | Three bearings |
| --- | --- |
| 1,11,13 | 143/15, 17/3, 899/60 |
| 1,11,19 | 143/15, 106/15, 199/12 |
| 1,13,19 | 17/3, 7/3, 179/15 |
| 11,13,19 | 57/5, 163/60, 241/15 |

In each row the three vectors of unit length have every cyclic bearing
gap less than 9. Thus the origin lies in the interior of the triangle
of unit vectors (otherwise a line through zero puts them in a closed
semicircle). Strictly positive coefficients sum them to zero; laying
out the three scaled vectors gives a nondegenerate planar triangle
with precisely those bearings. Membership in D_ij ensures both endpoint
row constraints. The quartet therefore tests compatibility *between*
realizable triangles.

To realize any subset, one must delete at least one vertex of each bad
cycle. The first and last cycles are disjoint from each other and from
the union of the three middle cycles. Those middle three have empty
total intersection, so hitting them requires at least two further
deletions. This proves 21−(1+2+1)=17 as an upper bound. We do not
assert a realization on 17 rows. The reasoning uses only options on the
surviving cycle edges and so is valid after vertex deletion.

The [new Fraction checker](scripts/check_unweighted_thresholds.py)
reconstructs the input from the pinned archive without running archived
code, checks all five semicircles and all four individual triangles,
and checks the disjointness used in the count. From this directory:

    python -B scripts/check_unweighted_thresholds.py artifacts/restore-20261105/jsp404-twentyseven-exact-20261104.zip

What remains for B is to force an obstruction in *every* hypothetical
21-point configuration, not to remove more rows of this example.
