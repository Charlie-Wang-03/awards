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
configurations; the counterexample here directly addresses the corresponding
fixed-parameter **ordinary-centre** inequality. No equivalence to the source's
exact-GA perfect-GC hypothesis is silently assumed.

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

## Consequence for the proof route

Do not repair the general upper branch by importing the printed s=4
maximum as this ordinary-centre lemma, or by using its smaller allowance
in a terminal ledger. An actual geometric proof must permit simultaneous
exponents 2,2 at two centres and the two remaining exponent-zero centres.
This example supplies no missing global payment and does not settle any
unproved all-N branch. It strengthens the reason to target the capacity
inequality itself instead of the source's asserted extremizer shape.

Attribution: Sendov for the problem, capacity framework, and source profile;
this explicit rational witness and its verification were developed in the
Charlie-Wang-03 workspace with Codex assistance. No priority claim is made.
