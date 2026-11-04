# Ordinary-point sharpness constructions for every N >= 3

2026-11-05. This proves only the epsilon-sharpness / upper-bound half of
the original minimax problem. It does not prove the universal lower bound.
The argument is a complete written construction. The corresponding all-N
ordinary sharpness theorem is now locally Lean-verified through the pinned,
attributed external construction and `OriginalUpperBound.lean`; see
[EXTERNAL_PROOF_ATTRIBUTION.md](EXTERNAL_PROOF_ATTRIBUTION.md).

Write angle(u,v) for the unoriented Euclidean angle in [0,pi] between
nonzero vectors. The angle at y of a triple x,y,z is angle(x-y,z-y).
For a real direction theta write e(theta)=(cos(theta),sin(theta)).

## 1. Finite binary clusters and their limiting directions

Fix an integer d>=0 and unit vectors u_0,...,u_(d-1). For a bit word
x in {0,1}^d and 0<h<1/3, put

    B_h(x) = sum_(j=0)^(d-1) h^j x_j u_j.

For d=0 the word set has one member and the empty sum is zero. For
distinct words x,y, let r be their first differing coordinate. Factoring
the finite difference gives the exact identity

    B_h(x)-B_h(y)
      = h^r [(x_r-y_r)u_r
               + sum_(j>r) h^(j-r)(x_j-y_j)u_j].

The leading coefficient is +1 or -1. The norm of the tail is at most
sum_(q=1)^(d-1-r) h^q, which is less than h/(1-h)<1/2. Thus the
bracket is nonzero, and B_h is injective. The bracket converges to
(x_r-y_r)u_r as h tends to zero through positive values.

Positive scaling of either vector does not change its angle. Also the
angle is continuous at every pair of nonzero vectors: it is

    arccos((u dot v)/(norm(u)*norm(v))),

and inner product, norm, division by a nonzero denominator, and arccos
on [-1,1] are continuous. Consequently the angle at B_h(y) of each
fixed distinct triple of words has a limit determined by the two
leading signed unit vectors in the displayed differences.

If the first differing coordinates of x,y and z,y are the same r,
both x_r and z_r are the unique bit opposite to y_r. The two signs
are equal, so this limiting angle is zero. If those coordinates are
different, the limiting angle is between signed copies of two different
vectors u_r,u_s.

In particular, suppose A>=0 and for every r!=s and every sign choice,

    angle(plus_or_minus u_r, plus_or_minus u_s) <= A.

Every triple limit is then at most A. There are finitely many ordered
distinct triples. Given epsilon>0, continuity supplies a positive
threshold for each triple below which its angle is less than its limit
plus epsilon. Take the minimum of these finitely many thresholds and
1/3 (or just 1/3 if there are no triples). Any positive h below that
minimum gives an injective 2^d-point ordinary planar configuration with
every triple angle less than A+epsilon. This is a simultaneous bound
on all triples, not a separate choice of h for each one.

## 2. The dyadic construction

Let d>=2 and choose

    u_j = e(j*pi/d),       j=0,...,d-1.

Two different direction parameters differ by q*pi/d with
1<=q<=d-1. For equal signs the angle is q*pi/d; for opposite signs
it is pi-q*pi/d. Both are at most

    A_d = (1-1/d)*pi.

Section 1 therefore gives, for every epsilon>0, an ordinary configuration
of 2^d distinct points whose maximum angle is less than A_d+epsilon.
Any subset of N<=2^d points has the same angle bound.

## 3. Three root centres with binary clusters

We will also use the following direct extension of Section 1. Take finitely
many distinct root centres R_a. At centre a choose d_a unit directions and
the associated binary cluster B_(a,h). Define actual ordinary points by

    P_h(a,x) = R_a + h B_(a,h)(x),       x in {0,1}^(d_a).

For h<1/3, each B_(a,h)(x) has norm less than 3/2 (and is zero if
d_a=0). If m is the minimum distance between the distinct root centres,
choosing also h<m/3 ensures different root clusters are disjoint, since
the total displacement of a pair from their roots is less than 3h<m.
Within a root cluster injectivity follows from Section 1. Hence these are
exactly sum_a 2^(d_a) distinct ordinary points.

There are three cases for an ordered triple:

* If its points lie at three different roots, the two difference vectors
  converge to the corresponding nonzero root differences. The limiting
  angle is the ordinary angle of those roots.
* If exactly two points lie at one root a and the third lies at root b,
  the angle at the third point tends to zero: its two difference vectors
  have the same nonzero limit R_a-R_b. At either of the paired points,
  divide its internal difference by the appropriate positive power of h
  as in Section 1. That vector tends to a signed internal unit direction;
  the external difference tends to R_b-R_a. The limiting angle is the
  angle between these two nonzero vectors.
* If all three lie at the same root, translate by -R_a and scale by the
  positive factor 1/h. The angles are those in Section 1.

Suppose every root triple angle, every signed internal/external angle,
and every signed angle between distinct internal directions at one root
is at most A>=0. The three cases show that all ordinary triple angles
have limits at most A. Applying the same finite-minimum argument as in
Section 1, and also imposing h<m/3, gives for every epsilon>0 one ordinary
configuration of the stated cardinality with all angles less than A+epsilon.
No assertion that the limiting generalized configuration is itself a set
of distinct ordinary points is needed.

## 4. The 5*2^(n-2) construction

Fix an integer n>=2 and put

    lambda = 2*pi/(2*n+1),  beta=lambda/2,
    A = pi-lambda,
    R_A=(-1,0), R_B=(1,0), R_C=(0,tan(beta)).

Here 0<beta<=pi/5<pi/2, so the three roots are distinct and
noncollinear. Their triangle angles are beta,beta,pi-2*beta.
All are at most A=pi-lambda: the last is equal to A and
beta<=A follows from 3*beta<=pi (in fact beta<=pi/5).

Use d_A=d_B=n-1 and d_C=n-2, with internal direction parameters

    at A: beta+j*lambda,    j=1,...,n-1;
    at B: j*lambda,         j=1,...,n-1;
    at C: beta+j*lambda,    j=1,...,n-2.

An empty C list when n=2 means a singleton cluster, as specified earlier.
The projective parameters of the lines to other roots are respectively

    at A: 0, beta;
    at B: 0, pi-beta;
    at C: beta, pi-beta.

We verify all internal/external constraints explicitly. Use
pi=(n+1/2)*lambda and pi-beta=n*lambda.

At A, every internal theta satisfies

    beta+lambda <= theta <= pi-lambda.

Thus both theta-0 and theta-beta belong to [lambda,pi-lambda].
At B, lambda<=theta<=(n-1)*lambda. Its difference from 0 lies in
[lambda,pi-lambda], and

    lambda <= (pi-beta)-theta <= (n-1)*lambda <= pi-lambda.

For a C direction (which exists only when n>=3), write
theta=beta+j*lambda with 1<=j<=n-2. Then

    theta-beta = j*lambda in [lambda,pi-lambda],
    (pi-beta)-theta = (n-j-1/2)*lambda in [lambda,pi-lambda].

For the second inclusion its minimum is 3*lambda/2 and its maximum
(n-3/2)*lambda. This proves every claimed interval bound.

For any two nonparallel projective directions whose parameter difference
lies in [lambda,pi-lambda], choosing either sign on either line gives
an angle equal to that difference or its supplement. Both are at most
pi-lambda=A. Therefore the interval checks prove all signed
internal/external constraints from Section 3.

At a fixed root, two distinct internal parameters differ by q*lambda,
where 1<=q<=n-2 at A and B, and 1<=q<=n-3 at C. Any such
difference again lies in [lambda,pi-lambda]. Thus all signed
internal/internal angles also satisfy the same bound; when there are
fewer than two internal directions this condition is empty.

Every hypothesis of Section 3 is now checked. Its ordinary configurations
have exactly

    2^(n-1)+2^(n-1)+2^(n-2) = 5*2^(n-2)

points, and for every epsilon>0 their maximum angle can be made less than

    (1-2/(2*n+1))*pi + epsilon.

## 5. All legal cardinalities and the minimax upper bound

For N=3 take the equilateral triangle (0,0),(1,0),(1/2,sqrt(3)/2),
whose angles are pi/3. For N=4 take the four vertices of a square;
their maximum triple angle is pi/2.

For N>=5, choose the unique integer n>=2 with 2^n<N<=2^(n+1).
This includes dyadic N: when N=2^d, use n=d-1.

* If N<=2^n+2^(n-2)=5*2^(n-2), choose any N-point subset of
  the configuration from Section 4.
* If N>5*2^(n-2), apply Section 2 with d=n+1 and choose any
  N-point subset of its 2^(n+1)-point configuration.

In both cases, for every epsilon>0 there is an injective ordinary N-point
configuration with every angle less than the proposed classification value
plus epsilon. Subsets preserve both injectivity and the angle inequality.

To connect this to the canonical definition, let a(N) denote the proposed
value and let alpha(N) be the largest universally forced angle. If b>a(N),
apply the construction with epsilon=(b-a(N))/2>0. Every angle in that
configuration is then less than a(N)+epsilon<b, so b is not universally
forced. It follows that alpha(N)<=a(N). The reverse inequality is not
proved here; it is precisely the remaining universal lower-bound problem.

## Attribution and verification status

The binary-direction and three-centre constructions are Sendov's established
sharpness ideas, not a new priority claim. This direct ordinary-point
realization proof was written in the Charlie-Wang-03 workspace with Codex
assistance. Independent public Lean work already formalizes all-N upper
constructions (superpilot69, subsequently credited and used by aznikline's
submission #5131). No third-party source was copied into this document or
vendored into this repository. The pinned Lake dependency now supplies those
construction proofs. Our locally built wrapper transports them to injective
Fin N configurations and proves the precise correspondence with the geometric
extremum. It claims no new authorship of the construction. The unconditional
all-N lower bound and complete original-problem theorem remain unproved.
