import JSP000404Research.ProjectionQTTTAllNSupport
import JSP000404Research.SecondLayerFourSupportTerminal
import Mathlib.Tactic

/-!
# Planar Q/T/T/T support terminal

Upgrade the uniform four-second-layer support reduction from merely
"at least two support-two centres" to the actual two-way terminal used by the
remaining geometry:

* at least three support-two centres; or
* exactly two support-two centres and two support-one centres, with both
  support-two transition quotients equal to one and a hidden quotient n-1
  exposed at each.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_QTTT_four_secondLayer_support_terminal
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    {s x y z : ProjectionOrdered V}
    (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsSecond : centreExponent (C s) t = n - 2)
    (hxSecond : centreExponent (C x) t = n - 2)
    (hySecond : centreExponent (C y) t = n - 2)
    (hzSecond : centreExponent (C z) t = n - 2) :
    FourSecondLayerSupportTerminal
      (reindexedPoint_injective hp) t n C s x y z := by
  have hcapR :
      AngleCap (reindexedPoint p) lam := by
    intro a b c hab hac hbc
    apply hcap a.toOriginal b.toOriginal c.toOriginal
    · intro h
      apply hab
      exact ProjectionOrdered.toOriginal_injective h
    · intro h
      apply hac
      exact ProjectionOrdered.toOriginal_injective h
    · intro h
      apply hbc
      exact ProjectionOrdered.toOriginal_injective h
  exact four_secondLayer_support_terminal
    (p := reindexedPoint p)
    (reindexedPoint_injective hp)
    hcapR hn3 hdelta0 hdeltaHalf ht hlam C
    hsx hsy hsz hxy hxz hyz
    hsSecond hxSecond hySecond hzSecond

#print axioms planar_QTTT_four_secondLayer_support_terminal

end ProjectionOrdered
end JSP000404Research
