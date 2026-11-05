# Separate affine maps do not restore the width-drop recursion

Research continuation, 2026-11-05. This is a counterexample to an intermediate
recursion. The original Blumenthal classification remains open in this project.

There is an explicit set S of twenty integer planar points such that

1. Every triple angle of S is strictly smaller than 18*pi/23.
2. For every partition S=S0 union S1, one part has an angle greater than
   13*pi/18 in every nonsingular affine image.

Thus the proposed step from t=23/5 to t-1=18/5 fails even when each part can
choose its own affine map. The twenty points respect the proposed original
upper-strip capacity of twenty.

## Exact data and finite check

The coordinates and 296 certificates are in
`verification/affine-partition-20261105/cover.json`, SHA-256
`2d47a2c1cebea734a70c5f12cd09f408bedcd2bbc581d368a03d1ffbcc5bf06a`.
Each certificate lists two or three ordered angle triples and the bit mask of
their combined vertex set. The triples use zero-based indices in the point list.

Run from the research directory

```powershell
python -B scripts/check_affine_partition_obstruction.py
```

The checker uses integer and rational arithmetic. It verifies all 3,420
angles, reconstructs every matrix and its weights, and exhausts the 524,288
colourings with vertex zero assigned colour zero. Swapping the two colours
covers the remaining colourings. Every colouring makes at least one entire
certificate carrier monochromatic. Empty parts are included.

The stored output is `verification/affine-partition-20261105/check.log`.
The script needs the Python standard library and the existing local rational
checker modules. Z3 and the numerical optimization code were used to discover
and shorten the certificate list. The verification script reads neither of
their outputs beyond the explicit integer coordinates and angle-triple indices
in the certificate data.

## Why each certificate controls every affine map

For an angle with nonparallel arms u,v at its middle vertex, set

    B = -(u*v^T + v*u^T) / (2*abs(det(u,v))).

Its determinant is -1/4. For any nonsingular linear map L, set
Q=L^T*L/abs(det L). This is positive definite with determinant one, and

    -cot(angle(Lu,Lv)) = tr(Q*B).

Translations disappear in the arm differences. A convex average C of angle
matrices therefore gives

    max_certified_angles -cot(angle_after_L) >= tr(Q*C).

For each stored certificate the checker constructs nonnegative rational
weights of sum one and verifies

    C_00 > 0,       4*det(C) > 3/4.

These conditions imply C is positive definite. For a two-angle support the
weights are 1/2,1/2. For a three-angle support the checker solves the two linear
stationarity equations using the determinant polarization

    polar(U,V)=tr(adj(U)*V).

It then checks the weights and determinant directly. The stationarity equations
serve only to produce the weights. The lower-bound argument uses the checked
inequalities and remains valid independently of any optimality assertion.

For completeness, the trace bound follows from an elementary identity. Write
C=[[a,b],[b,c]], Q=[[x,y],[y,z]], and s=sqrt(det C)>0. Since det Q=1,

    a*z*(tr(Q*C)-2*s) = (a-s*z)^2 + (a*y+b*z)^2 >= 0.

Both a and z are positive. Hence tr(Q*C)>=2*s>sqrt(3)/2. The scalar identity,
its inequality, and equality conditions are formalized in `AffineTraceBound`.

The rational arctangent enclosures also verify

    atan(7/6) < 5*pi/18,       (6/7)^2 < 3/4.

Since tangent is increasing on (0,pi/2), cot(5*pi/18)<6/7<sqrt(3)/2.
Negative cotangent is strictly increasing on (0,pi). It follows that at least
one of the certificate's angles, after any affine map, exceeds 13*pi/18.
Its entire carrier lies in one part of each partition, proving assertion 2.

## Why the original coordinates obey the parent cap

For every triple the integer arm determinant is nonzero. If its dot product is
nonnegative, its angle is at most pi/2<18*pi/23. Otherwise its angle equals
pi-atan(abs(det)/(-dot)). The checker verifies

    atan(abs(det)/(-dot)) > 5*pi/23

using the same rational alternating-series and Machin bounds documented in
`FULL_BAND_PHASE_COUNTEREXAMPLE.md`. Every inequality is strict. This proves
assertion 1 for the actual supplied integer coordinates.

## Verification scope and continuation

The complete geometric counterexample currently has a written proof with exact
executable arithmetic. Its full Lean geometry formalization is pending. The
scalar trace lemma has a separate kernel check. This does not settle the
original all-N lower bound.

The starting shape uses the already attributed twenty-point sharpness
construction, followed by rational coordinate selection and an independent
all-angle check. This workspace supplies the affine-partition obstruction and
the rational certificates. The construction attribution remains recorded in
`SHARPNESS_CONSTRUCTIONS.md` and `EXTERNAL_PROOF_ATTRIBUTION.md`.

Further recursion work must address a smaller domain, such as a minimal
overweight counterexample, or justify a different geometric transformation.
The one-top upper-strip ordered-direction conjecture in
`NARROW_OBSERVER_CAPACITY.md` remains a separate live target.
