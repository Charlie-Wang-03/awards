# A direct two-part angle-width recursion is false

2026-11-05. This is an exact geometric refutation of a proposed proof route,
not a refutation of Blumenthal's classification. It is not yet Lean-certified.

The candidate was: if a finite planar point set has all angles at most
pi-pi/t, partition it into two sets, each of which has all angles at most
pi-pi/(t-1). Iterating such a statement would give a tempting doubling
recurrence. The candidate fails in the lower strip at t=10/3=3+1/3,
and in the upper strip at t=15/4=3+3/4. In fact a five-point family
below refutes it for every real t with 3<t<4. It cannot replace either
global capacity theorem.

## Five integer points

Label the following distinct points 0 through 4:

    (-10297,-505), (-10303,-495), (-9697,495),
    (-9703,505), (9703,-505).

Every triple has an obtuse angle whose cosine is strictly between -4/7
and -2/5. Here is an exact certificate. At the listed vertex j of a triple,
write u=p_i-p_j, v=p_k-p_j, D=u dot v, U=u dot u, V=v dot v.

| Triple | j | D | U | V |
| --- | --- | ---: | ---: | ---: |
| 012 | 1 | -6264 | 136 | 1347336 |
| 013 | 1 | -6400 | 136 | 1360000 |
| 014 | 0 | -120000 | 136 | 400000000 |
| 023 | 2 | -6400 | 1360000 | 136 |
| 024 | 2 | -10640000 | 1360000 | 377360000 |
| 034 | 3 | -10507064 | 1372936 | 377612936 |
| 123 | 2 | -6264 | 1347336 | 136 |
| 124 | 2 | -10766400 | 1347336 | 377360000 |
| 134 | 3 | -10633600 | 1360000 | 377612936 |
| 234 | 2 | -126400 | 136 | 377360000 |

In every row U,V>0, D<0, and the integer inequalities are

    4*U*V < 25*D^2,        49*D^2 < 16*U*V.

Therefore -4/7 < D/sqrt(U*V) < -2/5. This is the cosine of the
listed angle. It is obtuse and is the largest angle of its triangle;
the other two angles are acute. No approximate arccosine value is used.
The table contains all ten unordered triples, so it checks all angles.

## Parent cap holds and every child triple fails

The parent cap at t=10/3 is 7*pi/10. The identity

    sin(pi/5)^2 = (5-sqrt(5))/8

and sqrt(5)<117/49 imply sin(pi/5)>4/7. The latter square-root
inequality follows by squaring positive numbers: 5*49^2=12005<13689=117^2.
Consequently cos(7*pi/10)=-sin(pi/5)<-4/7. Strict monotonicity
of cosine on [0,pi] proves that all the listed angles, and hence every
angle of this five-point set, are less than 7*pi/10.

The proposed child cap is 4*pi/7. We have

    cos(3*pi/5) = (1-sqrt(5))/4 > -2/5,

since sqrt(5)<13/5. Thus each listed obtuse angle is greater than
3*pi/5, which is itself greater than 4*pi/7. Every triple violates
the child cap. In any partition of five points into two classes, one
class contains at least three points, so no proposed partition works.

This excludes the recursion for unchanged point subsets. It does not
exclude a new construction that changes directions or moves points and
proves all necessary geometric properties. Such a construction would be
a separate missing theorem, not a consequence of taking subsets.

## The same integer witness also excludes the upper-strip recursion

In every row of the table the stronger integer inequality

    81*U*V < 400*D^2

holds. Thus the listed angle has cosine less than -9/20. At t=15/4
the parent cap is 11*pi/15 and the child cap is 7*pi/11. The already
proved parent bound 7*pi/10 is smaller than 11*pi/15. Also

    cos(7*pi/11) = -sin(3*pi/22) > -3/7 > -9/20,

using sin(x)<x for x>0 and pi<22/7. Therefore every triple's listed
angle is greater than the child cap 7*pi/11. The same five integer
points refute a recursion restricted to the upper strip, without relying
on the lower-strip example or on numerical trigonometric evaluation.

For completeness, the elementary bound pi<22/7 follows from positivity of

    integral_0^1 x^4*(1-x)^4/(1+x^2) dx = 22/7 - pi.

Polynomial division gives the integrand as
`x^6-4*x^5+5*x^4-4*x^2+4-4/(1+x^2)`, which evaluates the integral.

## A counterexample family for every 3<t<4

This stronger existence argument explains why moving the recursion to a
different part of either strip cannot repair it. Set

    u0=(1,0), u1=(1/2,sqrt(3)/2), u2=(-1/2,sqrt(3)/2),
    p_b(h)=b0*u0+h*b1*u1+h^2*b2*u2,

for the five binary strings `000,001,010,100,111`, where 0<h<1/2.
These are five distinct points: the first nonzero coefficient of a
difference has norm h^k, and the norm of its remaining tail is at most
`h^(k+1)/(1-h)<h^k`.

Consider any three of these binary strings. At their first differing
coordinate k, exactly two agree; call that pair b,c and the remaining
string a. The first differing coordinate l of b,c satisfies l>k.
After division by h^k, both vectors from a to b,c converge to the same
nonzero signed u_k. After division by h^l, the vector from b to c
converges to a nonzero signed u_l. Consequently the angle at a tends
to zero. The two other angles tend to theta and pi-theta, where theta
is the angle between signed u_k and signed u_l. Distinct directions
among u0,u1,u2 differ by pi/3 or 2*pi/3, so these two limits are
pi/3 and 2*pi/3 in some order. This uses angle continuity only on
nonzero limiting vectors; positive rescaling does not change an angle.
Thus the maximum angle of each of the ten triples tends to 2*pi/3.

For fixed 3<t<4, write A=pi-pi/t and B=pi-pi/(t-1). Direct comparison
gives `B<2*pi/3<A`. Choose

    epsilon = min(A-2*pi/3, 2*pi/3-B)/2 > 0.

For each triple, the limit just proved supplies a positive h-bound
under which its maximum angle differs from 2*pi/3 by less than epsilon.
Take h positive and smaller than 1/2 and all ten bounds. Every angle
of the five-point configuration is then less than A, while every triple
has an angle greater than B. One part of any two-part partition has
three points and therefore violates the proposed child cap.

This proves failure for every 3<t<4, including both open parameter
strips. It does not claim failure of a geometric transformation that
moves points, or of an induction with additional justified hypotheses.
The family is a written mathematical proof; no Lean formalization of
this counterexample is claimed.

## Sixteen points exclude the recursion for every t>4

The obstruction is not confined to the n=3 induction step. It persists for
every real t>4, so supplying finitely many small base cases does not repair
this unchanged-subset recursion.

First fix 0<beta<pi/2 and put

    u0=e(0), u1=e(beta), u2=e(pi/2), u3=e(pi/2+beta),
    p_b(h)=sum_(j=0)^3 h^j*b_j*u_j,     b in {0,1}^4.

Here e(theta)=(cos(theta),sin(theta)) and 0<h<1/4. The first differing
coordinate argument above proves that these sixteen points are distinct.
After positive rescaling, each difference vector is a signed unit u_j
plus an error of norm less than r=h/(1-h)<1. Its angle d from that signed
unit lies in [0,pi/2), because their inner product is positive. Resolving
the error into parallel and perpendicular components gives

    tan(d) < r/(1-r) = h/(1-2*h),
    d <= tan(d) < h/(1-2*h).

The inequality d<=tan(d) follows, for example, by differentiating tan(d)-d
on [0,pi/2). The angle between two vectors changes by at most the sum of
their angular changes: this is the triangle inequality for shortest arc
distance on the unit circle. Thus every triple angle differs from its
leading-vector angle by less than E=2*h/(1-2*h).

For three distinct words, their first splitting level k separates one word
from a pair; that pair first splits at a later level l. Their leading-vector
angles are 0, theta, pi-theta for the two directions u_k,u_l. All these
angles are at most

    L = pi - min(beta, pi/2-beta).

If (k,l) is (0,1) or (2,3), the largest leading-vector angle is pi-beta.
Call these designated triples. Every two-colouring of the sixteen words
has a monochromatic designated triple, as follows.

Group the words by their first two bits, giving four groups of four words.
Every triple inside one group has levels (2,3). If none of these triples
is monochromatic, each group must contain exactly two words of each colour.
Choose one word of colour zero from each of groups 00, 01, and 10. These
three words have splitting levels (0,1), so they form a monochromatic
designated triple after all. This argument includes partitions with an
empty part, since such a partition already fails inside each group.

Now let t>4, lambda=pi/t, lambda'=pi/(t-1), A=pi-lambda, B=pi-lambda'.
Since lambda<pi/4 and lambda'>lambda, the interval

    lambda < beta < min(lambda', pi/2-lambda)

is nonempty; choose its midpoint. Then min(beta,pi/2-beta)>lambda,
so L<A, while pi-beta>B. Let

    m=min(A-L, pi-beta-B)>0,
    h=min(1/8,m/16)>0.

This h is less than 1/4, and

    E=2*h/(1-2*h) <= (8/3)*h <= m/6 < m/2.

Consequently every angle of the sixteen-point set is less than L+E<A.
Every designated triple has an angle greater than pi-beta-E>B. The
colouring argument therefore prevents any partition into two unchanged
subsets both satisfying the child cap B. This is a genuine ordinary-point
counterexample for each t>4, not an abstract colouring offered as geometry.

## One explicit algebraic set works in both n=4 strips

Take beta=pi/4 and h=1/100. Multiplying all points by the positive factor
2*10^6 gives the following exact sixteen-point set, indexed by four bits:

    x_b=2000000*b0 + 10000*sqrt(2)*b1 - sqrt(2)*b3,
    y_b=10000*sqrt(2)*b1 + 200*b2 + sqrt(2)*b3.

Here L=pi-beta=3*pi/4 and the preceding angular error bound is E=1/49.
Since pi>3 and 68<3*49, we have E<pi/68. At lower-strip t=17/4,
the parent and child caps are respectively 13*pi/17 and 9*pi/13;
their margins around L are

    13*pi/17-L=pi/68,       L-9*pi/13=3*pi/52.

At upper-strip t=19/4 the caps are 15*pi/19 and 11*pi/15, with margins

    15*pi/19-L=3*pi/76,     L-11*pi/15=pi/60.

All four margins are at least pi/68. Thus the same exact set satisfies
both parent caps strictly, while every partition has a designated triple
violating the corresponding child cap strictly. No floating-point
trigonometric computation enters this certificate.

These arguments do not address the isolated parameter t=4. They exclude
the unrestricted unchanged-subset step for every 3<t<4 and every t>4;
in particular, starting that step at n>=4 cannot rescue it. They neither
refute the original minimax classification nor rule out a different
induction with a proved geometric transformation.

## Exact arithmetic replay

The companion script `scripts/check_width_drop_counterexample.py` recomputes
the table from integer coordinates, checks every inequality using integers,
and exhausts all 32 two-colour assignments. It also computes the 272
designated triples among four-bit words and exhausts all 65,536 colourings.
It checks these finite certificates;
the trigonometric deductions above are part of the written proof. It is
not a Lean kernel certificate and does not change the unresolved main DAG.

Attribution: this witness and its exact verification were developed in the
Charlie-Wang-03 workspace with Codex assistance. The limiting family uses
the standard binary separation construction also discussed and attributed
in [SHARPNESS_CONSTRUCTIONS.md](SHARPNESS_CONSTRUCTIONS.md). No priority
claim is made for that construction or the counterexample.
