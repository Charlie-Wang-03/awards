import JSP000404Research.FourSupportTwoAngleCore
import JSP000404Research.SmallPairAmongOtherThree

/-!
# Four local small-pair choices reduce to nine derangement patterns

This module is the geometry-facing, dependency-light wrapper around the
kernel-checked four-choice core.

Each of four distinct vertices supplies one delta*lambda-small pair among the
other three vertices.  The angle-cap collision theorem rules out two selected
small angles in the same triangle.  Therefore the four choices use the four
triangles exactly once, leaving exactly the nine K4 derangement patterns.

The separate second-layer bridge proving that a support-two centre actually
supplies such a small pair lives outside this file.  This keeps the finite
four-centre terminal independently kernel-checkable.
-/

namespace JSP000404Research

def FourSupportTwoDerangementPattern9
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  FourSupportTwoAnglePattern9Core p delta lam a b c d

theorem four_smallPairAmongOtherThree_reduce_to_derangement_nine
    {V : Type*}
    {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : SmallPairAmongOtherThree p delta lam a b c d)
    (hb : SmallPairAmongOtherThree p delta lam b a c d)
    (hc : SmallPairAmongOtherThree p delta lam c a b d)
    (hd : SmallPairAmongOtherThree p delta lam d a b c) :
    FourSupportTwoDerangementPattern9 p delta lam a b c d := by
  unfold SmallPairAmongOtherThree at ha hb hc hd
  simpa [FourSupportTwoDerangementPattern9] using
    (four_small_pair_choices_reduce_to_angle_derangement_nine_core
      hp hcap hdeltaHalf hlampos
      hab hac had hbc hbd hcd
      ha hb hc hd)

#print axioms four_smallPairAmongOtherThree_reduce_to_derangement_nine

end JSP000404Research
