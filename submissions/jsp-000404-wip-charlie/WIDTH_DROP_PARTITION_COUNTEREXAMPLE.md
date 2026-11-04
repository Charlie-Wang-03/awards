# A direct two-part angle-width recursion is false

2026-11-05. This is an exact geometric refutation of a proposed proof route,
not a refutation of Blumenthal's classification. It is not yet Lean-certified.

The candidate was: if a finite planar point set has all angles at most
pi-pi/t, partition it into two sets, each of which has all angles at most
pi-pi/(t-1). Iterating such a statement would give a tempting doubling
recurrence. The candidate fails even in the lower strip, at
t=10/3=3+1/3. It cannot replace the global payment theorem.

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

## Exact arithmetic replay

The companion script `scripts/check_width_drop_counterexample.py` recomputes
the table from integer coordinates, checks every inequality using integers,
and exhausts all two-colour assignments. It checks a finite certificate;
the trigonometric deductions above are part of the written proof. It is
not a Lean kernel certificate and does not change the unresolved main DAG.

Attribution: this witness and its exact verification were developed in the
Charlie-Wang-03 workspace with Codex assistance. No priority claim is made.
