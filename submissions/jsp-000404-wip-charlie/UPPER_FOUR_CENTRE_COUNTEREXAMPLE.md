# An actual planar counterexample to the stronger four-centre upper profile

2026-11-05. This refutes a proposed intermediate bound, **not** Blumenthal's
classification and **not** the upper capacity bound 2^n + 2^(n-2).
The argument below is an exact natural-language proof. It has not yet been
formalized with the project's `CentreProjectiveCycle` definitions.

The source-motivated strengthening being tested is:

> For four actual centres satisfying AngleCap at t=n+delta,
> 1/2<=delta<1, the sum of 2^(centreExponent) is at most
> 2^n + 2^(n-3).

This is the numerical maximum printed in Sendov's Acta 1995 proof of Lemma
4.1, case c.2, p. 39. The source is phrased using perfect generalized
configurations. The first part below refutes the corresponding fixed-parameter
ordinary-centre inequality. A separate construction below supplies an actual
perfect generalized configuration with exactly the source's prescribed
maximum angle, so the printed four-centre maximum is also false as stated.

## Configuration

Use the four distinct rational points

    A=(-1,0), B=(1,0), C=(0,1/2), D=(0,3/5),
    n=3, delta=3/4, t=15/4, lambda=4*pi/15.

Put a=arctan(1/2) and b=arctan(3/5). We will use

    2*pi/15 < a < b < pi/5.

Here arctan is strictly increasing. Also arctan(x)<x for x>0, so
b<3/5<pi/5 by pi>3. For the lower bound, on 0<=x<=1/2,

    1/(1+x^2) >= 1-x^2,

with strict inequality for x>0. Integration gives

    a > 1/2 - (1/2)^3/3 = 11/24 > 44/105 > 2*pi/15,

where the last comparison follows from pi<22/7. Thus all inequalities
used below have strict margins; no floating-point floor decision is involved.

## All actual angles satisfy AngleCap

There are three unordered pairs of other points at each centre. Direct ray
directions give the complete table (reversing the two endpoints changes nothing):

| Centre | Its three unoriented angles |
| --- | --- |
| A | a, b, b-a |
| B | a, b, b-a |
| C | pi-2*a, pi/2+a, pi/2+a |
| D | pi-2*b, pi/2-b, pi/2-b |

At A and B all entries are below pi/5. At C, pi-2*a<11*pi/15,
and pi/2+a<7*pi/10<11*pi/15. At D, pi-2*b<pi-2*a and
pi/2-b<pi/2. Consequently every triple angle is strictly below
11*pi/15=pi-lambda. This verifies the genuine geometric cap, not just a
combinatorial colour model.

## Exact projective gaps and exponents

Projective directions are ray directions modulo pi. At A their sorted list
is [0,a,b]; at B it is [0,pi-b,pi-a]. At C it is
[a,pi/2,pi-a]; at D it is [b,pi/2,pi-b]. Thus the cyclic gaps are:

| Centre | Gaps, up to cyclic permutation | Floors of gap/lambda |
| --- | --- | --- |
| A | a, b-a, pi-b | 0, 0, 3 |
| B | pi-b, b-a, a | 3, 0, 0 |
| C | pi/2-a, pi/2-a, 2*a | 1, 1, 1 |
| D | pi/2-b, pi/2-b, 2*b | 1, 1, 1 |

For A/B, the two small gaps are positive and below pi/5<lambda. The large
gap is above 4*pi/5=3*lambda and below pi<4*lambda. For C/D,
pi/2-a and pi/2-b lie strictly between 3*pi/10 and 11*pi/30;
both endpoints lie between lambda and 2*lambda. Likewise 2*a and 2*b
lie strictly between lambda and 2*pi/5<2*lambda. This proves every floor
entry in the table.

The source and project use k=sum(max(floor(gap/lambda)-1,0)). Therefore

    (k_A,k_B,k_C,k_D)=(2,2,0,0),
    sum 2^k = 4+4+1+1 = 10.

The proposed stronger bound is 2^3+2^(3-3)=9, so it is false. The full
upper capacity bound is 2^3+2^(3-2)=10 and is respected with equality.

## Perfect-GC realization with the exact prescribed maximum

The ordinary centres alone have a strict cap, whereas the source uses
GA(V)=pi-lambda. The following construction supplies that equality; it does
not assume it from the preceding ordinary-point calculation.

At A use two internal projective directions

    theta_A1=b+lambda, theta_A2=b+2*lambda.

At B use

    theta_B1=lambda, theta_B2=2*lambda.

The inequality pi-b>3*lambda proved above puts both A directions inside
the gap (b,pi), at distance at least lambda from both ends. For every
external direction r in {0,a,b}, theta_Aj-r is between lambda and
pi-lambda. At B, each theta_Bj is at least lambda above 0 and at least
lambda below pi-b. For each r in {0,pi-b,pi-a}, the absolute difference
from theta_Bj is again between lambda and pi-lambda. Thus every internal
line is projectively separated by at least lambda from every line to a
different root centre. The two internal directions at either root differ
by exactly lambda.

Put disjoint small root circles at A,B,C,D. The C and D circles are
primitive. In the A circle place two child circles whose centre difference
has direction theta_A1. In each child place two primitive circles whose
centre difference has direction theta_A2. Do the analogous construction
at B. This gives four primitive leaves under A, four under B, and one
each at C,D: ten leaves in total. Every nonprimitive circle has exactly
two children. The two child contents at A are equivalent two-point GCs
because their oriented leaf differences agree in direction; the same is
true at B. All other nonprimitive circles have two singleton contents.
The resulting GC is therefore perfect under the source's definition.

Here is also how to satisfy the source's position and circle conditions,
without assuming that a parent centre is the midpoint of its children.
Choose each new pair of centres at a fixed sufficiently small positive
separation in the required direction, with its midpoint allowed to move
in a small open disk inside its parent. Given the finitely many previously
chosen centres, forbid the midpoint lines for which either new centre
lies on a line through two previous centres, and the lines parallel to
the pair direction for which a previous centre lies on the new pair's
line. These are finitely many lines and cannot cover an open disk: take
a line segment in a direction different from all of them and omit its
finitely many intersection points. Choose the midpoint on what remains.
Repeat for each pair. This ensures no three circle centres are collinear.
After selecting a sibling pair strictly inside a parent, choose positive
child radii less than one third of the sibling separation and less than
their positive distance to the parent's boundary. This ensures disjoint
sibling circles and strict containment. Subsequent choices are inside
these circles. Translating a pair's midpoint changes none of the specified
directions or the two-point equivalences, so it does not change the GC's
generalized directions. This constructs the required circle arrangement.

We can check its maximum generalized angle directly by the three possible
locations of a triple of leaves:

1. If the leaves belong to three different root circles, their generalized
   angles are ordinary angles of A,B,C,D, already proved below pi-lambda.
2. If exactly two leaves lie in one root circle, their internal direction
   is one of its two theta directions; the external direction is a line
   to another root centre. The separation inequalities above imply that
   either choice of ray signs gives an angle at most pi-lambda. The angle
   at the single external leaf is zero.
3. If all three leaves lie under A (or under B), two lie in the same child
   and the third in the other child. The internal pair uses theta_2,
   while the cross-child direction uses theta_1. Since their difference
   is lambda<pi/2, the two angles at the internal pair are lambda and
   pi-lambda, and the third generalized angle is zero.

The last case exists, and hence GA(V)=pi-lambda exactly. For the source's
parameter u=2*t=15/2 we have floor(u/2)=3 and delta=3/4, with four root
centres and ten points. This contradicts the printed case-c.2 maximum
2^3+2^(3-3)=9. It respects Lemma 4.1's full upper capacity of ten and
does not disprove that lemma's final inequality or the classification.

## Consequence for the proof route

Do not repair the general upper branch by importing the printed s=4
maximum, either as a perfect-GC assertion or as an ordinary-centre lemma,
or by using its smaller allowance
in a terminal ledger. An actual geometric proof must permit simultaneous
exponents 2,2 at two centres and the two remaining exponent-zero centres.
This example supplies no missing global payment and does not settle any
unproved all-N branch. It strengthens the reason to target the capacity
inequality itself instead of the source's asserted extremizer shape.

## The same obstruction occurs at every odd n >= 3

This is not restricted to n=3. Write n=2*r+1 with integer r>=1, and set

    delta=3/4, t=n+3/4, lambda=pi/t,
    a=3*lambda/5, b=7*lambda/10,
    A=(-1,0), B=(1,0), C=(0,tan(a)), D=(0,tan(b)).

We have 0<a<b<pi/2 because lambda<=4*pi/15. Thus tangent is strictly
increasing on this interval and the four points are distinct. The preceding
angle and projective-gap tables apply unchanged. Each actual angle is below
pi-lambda: pi-2*a<pi-lambda, pi-2*b<pi-lambda, and

    pi/2+a+lambda = pi/2+8*lambda/5
                    <= pi/2+32*pi/75 < pi.

The base angles satisfy b+lambda=17*lambda/10<=34*pi/75<pi;
the remaining angles pi/2-b are also below pi-lambda since
lambda-b=3*lambda/10<=2*pi/25<pi/2.

At either base, the scaled gaps are 3/5, 1/10, and n+1/20, hence the
quotients are 0,0,n and the exponent is n-1. At C the scaled gaps are

    r+11/40, r+11/40, 6/5,

and at D they are

    r+7/40, r+7/40, 7/5.

Their quotients are r,r,1, giving exponent 2*(r-1)=n-3 at both C and D.
Consequently the genuine geometric profile is

    [n-1,n-1,n-3,n-3],
    sum 2^k = 2^n + 2^(n-2) > 2^n + 2^(n-3).

This family saturates the full proposed upper capacity at every odd n>=3
while violating the smaller four-centre estimate. No numerical search or
unproved geometric feasibility premise is used in this derivation.
Its Lean formalization remains outstanding.

Attribution: Sendov for the problem, capacity framework, and source profile;
this explicit rational witness and its verification were developed in the
Charlie-Wang-03 workspace with Codex assistance. No priority claim is made.
