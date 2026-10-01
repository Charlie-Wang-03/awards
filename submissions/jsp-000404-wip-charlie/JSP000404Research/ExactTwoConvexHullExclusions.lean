import JSP000404Research.StrictExposureConvexHull
import JSP000404Research.SupportLeTwoTransitionInterval
import Mathlib.Tactic

/-!
# Convex-hull exclusions for the exact-two four-centre terminal

Every support-one or support-two centre has quotient support at most two.
The concrete transition interval theorem therefore makes every one of the
four exact-two centres strictly exposed in the full point configuration.

Consequently none of the four selected points belongs to the convex hull of
the other three selected points.
-/

namespace JSP000404Research

theorem exactTwo_four_centres_convexHull_exclusions
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t : ℝ}
    (ht : 0 < t)
    (htone : 1 ≤ t)
    (hlam : lam = Real.pi / t)
    {o₁ o₂ s₁ s₂ : V}
    (ho12 : o₁ ≠ o₂)
    (ho1s1 : o₁ ≠ s₁) (ho1s2 : o₁ ≠ s₂)
    (ho2s1 : o₂ ≠ s₁) (ho2s2 : o₂ ≠ s₂)
    (hs12 : s₁ ≠ s₂)
    (Co1 : CentreProjectiveCycle hp o₁)
    (Co2 : CentreProjectiveCycle hp o₂)
    (Cs1 : CentreProjectiveCycle hp s₁)
    (Cs2 : CentreProjectiveCycle hp s₂)
    (ho1Support :
      positiveSupport (centreQuotient Co1 t) = 1)
    (ho2Support :
      positiveSupport (centreQuotient Co2 t) = 1)
    (hs1Support :
      positiveSupport (centreQuotient Cs1 t) = 2)
    (hs2Support :
      positiveSupport (centreQuotient Cs2 t) = 2) :
    p o₁ ∉ convexHull ℝ ({p o₂,p s₁,p s₂} : Set Plane) ∧
    p o₂ ∉ convexHull ℝ ({p o₁,p s₁,p s₂} : Set Plane) ∧
    p s₁ ∉ convexHull ℝ ({p o₁,p o₂,p s₂} : Set Plane) ∧
    p s₂ ∉ convexHull ℝ ({p o₁,p o₂,p s₁} : Set Plane) := by
  have ho1Expose :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap ht htone hlam o₁ Co1
      (by rw [ho1Support]; omega)
  have ho2Expose :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap ht htone hlam o₂ Co2
      (by rw [ho2Support]; omega)
  have hs1Expose :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap ht htone hlam s₁ Cs1
      (by rw [hs1Support]; omega)
  have hs2Expose :=
    strictlyExposedAt_of_positiveSupport_le_two
      hp hcap ht htone hlam s₂ Cs2
      (by rw [hs2Support]; omega)
  exact four_strictlyExposed_convexHull_exclusions
    ho12 ho1s1 ho1s2 ho2s1 ho2s2 hs12
    ho1Expose ho2Expose hs1Expose hs2Expose

#print axioms exactTwo_four_centres_convexHull_exclusions

end JSP000404Research
