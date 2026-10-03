import JSP000404Research.SharpCentre

/-!
# Lightweight four-point small-pair interface

This proposition records the local geometric output needed from a support-two
centre: among three other marked vertices, one of the three visible pairs
subtends a delta*lambda-small angle at the centre.

It is deliberately separated from the projective-cycle proof producing the
small pair, so finite four-centre geometry can be kernel-checked without
importing the older Q/T/T/T and Hall infrastructure.
-/

namespace JSP000404Research

def SmallPairAmongOtherThree
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam
  ∨ EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam
  ∨ EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam

end JSP000404Research
