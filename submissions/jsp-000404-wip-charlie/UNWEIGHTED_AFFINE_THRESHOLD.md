# Ordinary points: a certificate using at most three angles

Research continuation, 2026-11-05. **A and B are open in general.** This
is a written reduction and a partial result for A, not a Lean proof of the
cardinality bounds. Write λ = 2π/(2n+1) for A, or λ = π/(n+1) for B.
In both cases the cap is strict, at π−λ. A putative counterexample can
be restricted to exactly the first forbidden cardinality, since passing to
a subset preserves the cap. No three of its points are collinear.

## 1. An affine certificate for a particular set

Let S have at least five points, with no three collinear. For an angle
with arms u,v based at its middle vertex, form the real symmetric matrix

    B(u,v) = −(uvᵀ + vuᵀ)/(2 |det(u,v)|).

Use all three angles of every triangle. Each B has determinant −1/4
(expand in coordinates) and trace −cot(angle). For a linear map L with
|det L|=1, B(Lu,Lv)=L B(u,v) Lᵀ. Translations and uniform scalings do
not affect angles. Thus, for a positive definite symmetric matrix Q of
determinant 1, the largest negative cotangent after an affine change
with LᵀL=Q is

    f(Q) = max_B tr(QB).

**Certificate theorem.** For 0<λ<π/2, the following are equivalent:

1. Every nonsingular affine image of S has an angle at least π−λ.
2. There are at most three actual angles of S and nonnegative weights
   summing to 1 for which their matrix average C is positive definite and
   4 det C ≥ cot² λ.

The weights in this statement combine at most three *angles of this
ordinary point set*. They are not centre multiplicities or capacities.
More precisely, there is such a positive definite average attaining
2√det C = min_Q f(Q) whenever that minimum is positive.

*Proof of sufficiency.* For all such Q,

    max_B tr(QB) ≥ tr(QC) ≥ 2√det C,

by applying arithmetic-geometric mean to the two eigenvalues of
Q^(1/2) C Q^(1/2). Negative cotangent is strictly increasing on (0,π).

*Existence of a minimizer.* If Q escapes all compact subsets of the
determinant-one positive definite matrices, pass to a subsequence with
largest eigenvalue t tending to infinity and its unit eigenvector tending
to e (choose signs and a subsequence). There must be at least three
distinct projections of S on e: otherwise two lines perpendicular to e
would cover S, impossible with five points and no three collinear. Choose
points with three strictly ordered projections and take both arms at the
middle one. Their projections on e have strictly opposite signs, so
eᵀBe>0. In the moving eigenbasis tr(QB)=t e_tᵀBe_t + O(1/t) tends to
infinity. This rules out every unbounded minimizing sequence, and f is
continuous. Its minimum is attained.

*Necessity and the number three.* Apply a minimizing affine map to S;
now Q=I minimizes f. Put c=f(I). All active matrices have trace c.
The origin belongs to the convex hull of their traceless parts
B−(c/2)I. Otherwise strict separation in the two-dimensional real
space of traceless symmetric matrices supplies a traceless symmetric H
with tr(HB)<0 for every active B. Along Q(s)=exp(sH) each active value
then decreases at s=0, and the finitely many inactive values start
strictly below c. This contradicts minimality. In a plane a point in a
finite convex hull is in the hull of at most three of its points
(a minimal convex representation has affinely independent support).
Hence an average of at most three active B equals (c/2)I. When (1)
holds, c≥cot λ>0. Undoing the change of basis preserves definiteness
and determinant and gives (2), including equality at the threshold. □

**What this changes in the proof problem.** For each n, A (respectively
B) is equivalent to the following selection problem: any set of 2^n+1
(respectively 5·2^(n−2)+1) points with no three collinear supplies the
certificate in (2). If there is a collinear triple, its middle angle is
already π. Indeed the class of all such real point sets is
closed under nonsingular affine maps. Conversely any certificate works
for the original coordinates by sufficiency. Only the union of at most
nine points is required to certify the entire affine class. Equivalently,
if each subset of at most nine points of a fixed S can separately be
affinely moved below the cap, one affine map moves the whole S below it.
This last assertion is about subsets of **one** set, not arbitrary sets
of nine points. For the selection problem it also suffices to prove (2)
for rational coordinates: an ordinary strict counterexample can be
approximated by rational points while preserving injectivity and all the
finitely many strict inequalities. Its own identity affine map would
then contradict (2). No selection theorem at either required cardinality
is proved here.

**Exact arithmetic and an obstruction to a pair-only test.** The
certificate search for a given rational S has rational data. For a
minimal support attaining c>0, the minimizing coordinates above give
C=(c/2)Q_*^(−1) in the original frame. There is a finite test that
does not require searching over real weights:

- For two distinct angles test their midpoint. In minimizing coordinates
  the two traceless parts have the same norm: for an active matrix
  B=(c/2)I+[[x,y],[y,−x]], x²+y²=(1+c²)/4 follows from det B=−1/4.
  If two such vectors balance, they are opposite and their weights equal.
- For three angles solve tr(adj(C)(B_i−B_1))=0 for i=2,3, with the
  weights summing to one. The equations are necessary since adj(C) is
  proportional to Q_* and the three original traces tr(Q_*B_i) agree.
  The adjugate is linear in dimension two, so only a 2 by 2 linear
  system is needed. A minimal three-angle support gives a nonsingular
  system: after minimizing, B_2−B_1 and B_3−B_1 are independent
  traceless matrices. The form tr(adj(D)E) is negative definite on
  that plane (tr(adj(D)D)=2 det D=−2(x²+y²)). Its Gram matrix
  is therefore invertible. The form is preserved by determinant-one
  congruence, by polarizing the determinant. A singular triple can be
  skipped, since it is not needed for a minimal optimal support.

In both cases retain only nonnegative weights, C>0 and a sufficiently
large determinant. Sufficiency still applies to every retained choice.
There cannot be a positive definite one-angle certificate, since a
single B has negative determinant. This proves in particular that
c²=4 det C is rational for rational S when c>0. It gives no uniform
gap over rational configurations.

For an exact check it suffices to exhibit weights, C>0, and

    tr(adj(C)B) ≤ 2 det C   for every angle matrix B.

Indeed Q=adj(C)/√det C attains f(Q)≤2√det C, and sufficiency supplies
the opposite inequality. The [rational checker](scripts/check_unweighted_thresholds.py)
does this on the four rational centres, both six-point phase examples,
and the five-point width-drop example. In the four-centre example the
optimum is 120°: after scaling the y-coordinate by 2/√3 the three rays
at the interior point C are 120° apart. Only those three angles attain
the maximum: the other vertices' angles in the published table are
strictly smaller. Their three traceless matrices are equal-length vectors
at mutual angles 120° (the off-diagonal and diagonal difference transform
by twice the rotation angle). No pair balances. This last calculation
applies directly to those four points by the primal and dual check; it
does not require the five-point compactness argument. If an example with
at least five points is desired, a regular pentagon also needs three
angles to certify its affine optimum 108°: only the five hull ears attain
108°, their traceless parts rotate by 144°, sum to zero, and no two are
antipodal. Equality in the trace bound at I would require a certificate
supported on active angles with scalar average.

There are endpoint tests at n=4: the nine ears of the regular nonagon
have angle 140°, and the ten ears of the regular decagon have angle
144°. In either polygon averaging all ears gives a scalar matrix by
rotational symmetry. Three suffice by the same plane convex-hull
argument. These are tests at the two correct angular thresholds, not
cardinality proofs at 17 or 21. Conversely at the identity any strictly
capped S has tr B < cot λ for every B, so no positive definite average
can meet the certificate threshold. In particular it does not exclude
the previously verified four-centre geometry or its odd-n saturation
family. No bound of nine on its dyadic mass is used.

## 2. A restriction on every minimal counterexample to A

**Narrow view from one point.** Let z belong to a strictly capped S and
let T be a set of other points seen from z in an oriented cone [a,a+w],
with 0≤w<λ. Every projective direction determined by T lies in the
open interval (a+λ, a+w+π−λ) modulo π.

To prove it, order two rays by their arguments b<d. The direction e
from the first endpoint to the second has its lift in (d,b+π):
the displacement is the positive sum of vectors in directions d and
b+π, which span less than π. The two angles there are π−(e−b)
and e−d. The strict cap gives e>b+λ and e<d+π−λ. This proves
the assertion. Equal rays would give a collinear triple.

If all projective directions of T fit into k consecutive bands of width
at most λ, then |T|≤2^k. In one lifted band orient its edges forward.
A vertex cannot have both an incoming and an outgoing edge there: their
angle would be at least π−λ. Give it one bit recording its side, with
an arbitrary bit if isolated. The endpoints of each edge differ in its
band's bit. Assign boundary edges to just one band; strictness suffices.
This is the classical direction-colouring argument of
[Erdős and Szekeres, Section 4](https://renyi.hu/~p_erdos/1960-09.pdf).

For A take w≤λ/2. The remaining interval has length at most
π−3λ/2=(n−1)λ. Hence **every such view contains at most 2^(n−1)
other points**. In particular A holds if S has a partition into two
parts, each seen in a cone of aperture at most λ/2 from some member of
the other part; the observers and cone axes for the two parts may differ.
Any putative (2^n+1)-point counterexample lacks every such partition.
At n=4 no observer in it can see nine other points within 20°.

The exponent for a single view cannot be decreased. Put two very small
binary clusters far apart along direction 0. Inside either cluster use
successive binary scales in directions jπ/n, 1≤j≤n−1. Limiting lines
from distinct levels are separated projectively by at least π/n>λ;
in each triple two points separate at a finer level than the third, so
the two possibly large limiting angles are at most π−π/n. Strictness
persists for sufficiently small positive scales. Either cluster has
exactly 2^(n−1) points and is seen in an arbitrarily small cone from the
other. At n=4 the checker also verifies all 1,680 angles of a concrete
16-point integer instance and both eight-point views. This is an
application of the existing binary construction, not a new all-N
sharpness claim.

## 3. What failed, what remains, and sources

- [An ordinary Euclidean counterexample for every n≥64](UNWEIGHTED_SECTOR_COUNTEREXAMPLE.md)
  refutes a global partition into n triangle-free direction intervals,
  even allowing their widths to vary. It does not refute the narrow-view
  bound above or a statement restricted to overweight sets.
- [Five increasing cycles in the fixed 21-row model](UNWEIGHTED_ROW_CYCLES.md)
  exclude every 18-row subset of that particular model. They do not
  supply a forced cycle for arbitrary 21-point data.
- [Sendov's own publication list](https://parallel.bas.bg/~pencho/sendov/pap9bs.html)
  identifies Se92, C. r. Acad. Bulgare Sci. **45**(12), 17–20, and Se93,
  **46**(5), 27–30. The separate 1993 Blagoevgrad paper, pp. 10–24,
  also has a Bulgarian version in Fiz.-math. sp. **34**(2), 118–127.
  The [Bulgarian library catalogue](https://plus-legacy.cobiss.net/cobiss/bg/en/bib/nacid/1119631844)
  lists holdings including the 1993 issue; the [1994 proceedings contents](https://books.google.com/books/about/Advances_in_Parallel_Algorithms.html?id=vuQR8novQ5MC)
  list a further paper starting on p. 194. No readable general induction
  was obtained from these early sources. This is an access limitation,
  not a verdict on unread pages.
- In the [Russian 1995 primary text](https://www.mathnet.ru/eng/fpm81),
  Section 4.1 attributes the small 9–16 results to references 9–10
  and the general formula to 12–13. Lemma 4.12 on pp. 510–512 announces
  induction and then states both maximizing lists for s without deriving
  them from s−1. The [Acta 1995 scan](https://real-j.mtak.hu/7467/),
  Lemma 4.1, printed pp. 39–40, makes the same jump. These passages were
  re-read; the [four-centre counterexample](UPPER_FOUR_CENTRE_COUNTEREXAMPLE.md)
  also refutes the stronger upper-branch maximum used there.

The remaining selection problem is geometric: force the matrix certificate
at the forbidden size, or find a different unweighted argument. No new
unconditional arbitrary-n branch or Lean theorem follows. The verified
Lean source remains b24bf60107959020e7b29b6e1263b739509987b0; the
subsequent evidence commit is 040c691e903b2d845732914a1a17eb2cb1c0c0fd.
