# A common phase need not have at most one full-band vertex

This rules out a proposed sufficient condition for the original lower bound.
It does **not** refute the Blumenthal/Sendov classification. It is a complete
finite rational-interval certificate, **not a Lean-certified theorem**.

## Statement and integer configuration

Set `n=3`, `t=349/100`, `delta=49/100<1/2`, and `lambda=100*pi/349`.
Number the following six points from 0 to 5:

```
0 = ( 105,  13)     1 = ( 69, 69)     2 = (-72,  67)
3 = (-102,   1)     4 = (-47,-92)     5 = ( 48, -83)
```

Every triple angle is strictly less than `pi-lambda=249*pi/349`.
For a phase `phi` modulo `pi`, put an unoriented segment of direction `theta`
in bin

    floor(((theta-phi) mod pi)/lambda).

The four bins are `[0,lambda)`, `[lambda,2*lambda)`,
`[2*lambda,3*lambda)`, `[3*lambda,pi)`. A vertex is full if its five
incident segments meet all four bins. **Every phase has at least two full
vertices.** In particular, the proposed at-most-one-full phase need not exist
even for genuine planar points in the strict lower strip.

The six-point configuration is consistent with the required bound `6<=2^3`.
The abstract theorem `hansel_card_le_two_pow_of_atMostOne_full` remains valid;
its proposed geometric premise fails. The stronger every-vertex-missing
premise fails as well. A phase argument retaining the entire completion mass
is a different, still unproved possibility.

## Exact angle and event certificate

Run, from this research directory:

```powershell
python -B -X utf8 scripts/check_full_band_phase_counterexample.py
```

The checker uses only Python integer and `fractions.Fraction` arithmetic.
It does not call floating-point or numerical trigonometric routines.
Its enclosures follow from these explicit identities and inequalities:

1. For `0<=r<=1/2`, let `S_m(r)=sum_{k=0}^{m-1} (-1)^k*r^(2*k+1)/(2*k+1)`.
   The alternating-series theorem puts `atan(r)` between `S_24(r)` and
   `S_25(r)`, including their endpoints.
2. `pi=16*atan(1/5)-4*atan(1/239)` (Machin's identity). For completeness,
   `tan(4*atan(1/5))=120/119` and the tangent subtraction formula gives
   `tan(4*atan(1/5)-atan(1/239))=1`; the angle lies in `(0,pi/2)`.
3. For `r>1`, use `atan(r)=pi/2-atan(1/r)`. For `1/2<r<=1`, use
   `atan(r)=pi/4-atan((1-r)/(1+r))`. Thus every remaining series argument
   is between 0 and 1/2. Interval addition, subtraction and multiplication
   by rational constants preserve the enclosures.

For each vertex and unordered pair of other points, let `D` be the dot
product of the two integer rays and `K` the absolute determinant. All 60
tests give `K>0`, also proving that no triple is collinear. If `D>=0`, its
angle is at most `pi/2<pi-lambda`. If `D<0`, its angle is
`pi-atan(K/(-D))`; the checker's rational lower bound for that arctangent
strictly exceeds its rational upper bound for `lambda`. This proves the
claimed cap for all ordered triples as well, by endpoint symmetry.

There are 15 segment directions `theta_ab` in `[0,pi)`. The only possible
bin-change phases are

    E(ab,j) = (theta_ab-j*lambda) mod pi,   0<=a<b<=5, 0<=j<=3.

The checker encloses all 60 events in pairwise disjoint rational intervals
strictly inside `(0,pi)`, and verifies their cyclic order below. In each open
cell immediately after an event it selects a rational phase between the
bounding event intervals. For every segment, interval division by the
positive `lambda` bounds has the same floor at both ends, so its bin is
certified exactly. The bin of a segment is constant until the next listed
event, because the list contains all its possible crossings.

In this table `ab:j` denotes `E(ab,j)` and a digit string gives precisely
the vertices full in the following open cell. The last cell continues
through phase zero back to the first event.

| Cell | Event | Full | Cell | Event | Full | Cell | Event | Full |
|---:|:---:|:---:|---:|:---:|:---:|---:|:---:|:---:|
| 1 | 12:0 | 01 | 21 | 05:0 | 145 | 41 | 34:0 | 23 |
| 2 | 14:1 | 01 | 22 | 02:2 | 145 | 42 | 01:0 | 023 |
| 3 | 03:0 | 013 | 23 | 04:3 | 145 | 43 | 24:3 | 03 |
| 4 | 45:0 | 0134 | 24 | 23:0 | 1245 | 44 | 25:0 | 0235 |
| 5 | 05:1 | 1345 | 25 | 34:1 | 1235 | 45 | 12:1 | 0135 |
| 6 | 02:3 | 1345 | 26 | 01:1 | 0235 | 46 | 14:2 | 0135 |
| 7 | 23:1 | 1245 | 27 | 25:1 | 0235 | 47 | 03:1 | 0135 |
| 8 | 34:2 | 1235 | 28 | 12:2 | 0135 | 48 | 45:1 | 0134 |
| 9 | 01:2 | 0235 | 29 | 14:3 | 035 | 49 | 05:2 | 1345 |
| 10 | 13:0 | 0235 | 30 | 03:2 | 035 | 50 | 23:2 | 1245 |
| 11 | 25:2 | 0235 | 31 | 15:0 | 0135 | 51 | 34:3 | 125 |
| 12 | 12:3 | 0135 | 32 | 45:2 | 013 | 52 | 01:3 | 25 |
| 13 | 03:3 | 135 | 33 | 05:3 | 135 | 53 | 13:1 | 25 |
| 14 | 15:1 | 135 | 34 | 23:3 | 15 | 54 | 35:0 | 235 |
| 15 | 45:3 | 13 | 35 | 13:2 | 15 | 55 | 25:3 | 35 |
| 16 | 04:0 | 0134 | 36 | 24:0 | 1245 | 56 | 15:2 | 35 |
| 17 | 13:3 | 04 | 37 | 35:1 | 1245 | 57 | 02:0 | 0235 |
| 18 | 24:1 | 04 | 38 | 15:3 | 24 | 58 | 04:1 | 0235 |
| 19 | 35:2 | 04 | 39 | 02:1 | 24 | 59 | 24:2 | 0235 |
| 20 | 14:0 | 014 | 40 | 04:2 | 24 | 60 | 35:3 | 02 |

Every row has at least two full vertices. It remains to check event phases,
not merely generic phases. As `phi` increases through `E(ab,j)` with
`j=1,2,3`, that edge's bin changes from `j` to `j-1`; at the event itself,
the half-open convention gives `j`, the preceding value. At `j=0` it changes
from 0 to 3 and the event value is again the preceding value 0. Only one
edge changes at each event, by strict separation of all 60 event intervals.
Thus every event has exactly the full set of its preceding cell. At zero
no event occurs and the bins are periodic. This handles every phase.

The actual run ends with:

```
PASS: 60 strict angle checks; 60 disjoint event enclosures; full counts 2..4 in every open cell.
Every event inherits its preceding cell by the half-open convention.
Scope: exact rational interval certificate, NOT a Lean theorem.
```

The failed conjecture was a proposed route in this research workspace, not an
assumption of the original problem or a claim attributed to another author.
