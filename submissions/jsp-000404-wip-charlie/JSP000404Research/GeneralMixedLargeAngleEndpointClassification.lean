import JSP000404Research.GeneralMixedLargeAngleWitness
import JSP000404Research.GeneralMixedLargeAngleEndpointRestriction
import Mathlib.Tactic

/-!
# Endpoint classification for the large-angle witness in any mixed pattern

The true large-angle existence theorem produces two distinct OTHER vertices
at support-two centre b. The strict hidden-angle frontier restricts their
possible incidence with the sharp centre s: if either endpoint is s,
the opposite endpoint must be the support-one centre a.

Consequently one may select a real large-angle witness that either avoids s
entirely, is oriented s→a, or is oriented a→s. This is a genuine
arbitrary-cardinality localization of the remaining large-angle obstruction,
not a global payment or an unconditional mixed-pattern contradiction.
-/

namespace JSP000404Research

theorem general_mixed_large_angle_endpoint_classification
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (hS : centreExponent Cs t = n - 1)
    (hA : centreExponent Ca t = n - 2)
    (hB : centreExponent Cb t = n - 2)
    (hsupA : positiveSupport (centreQuotient Ca t) = 1)
    (hsupB : positiveSupport (centreQuotient Cb t) = 2) :
    ∃ x y : OtherVertex b,
      x ≠ y ∧
      (((n - 1 : ℕ) : ℝ) * lam) ≤
        EuclideanGeometry.angle (p x.1) (p b) (p y.1) ∧
      ((x.1 ≠ s ∧ y.1 ≠ s) ∨
        (x.1 = s ∧ y.1 = a) ∨
        (x.1 = a ∧ y.1 = s)) := by
  obtain ⟨x, y, hxy, hlarge⟩ :=
    general_mixed_actual_large_angle_exists
      hp hcap hn hdelta0 hdeltaHalf ht hlam
      hsa hsb hab Cs Ca Cb hS hA hB hsupA hsupB
  refine ⟨x, y, hxy, hlarge, ?_⟩
  by_cases hx : x.1 = s
  · right
    left
    have hy :=
      general_mixed_large_angle_sharp_endpoint_forces_support_one
        hp hcap hn hdelta0 hdeltaHalf ht hlam
        hsa hsb hab Cs Ca Cb hS hA hB hsupA hsupB
        x y hxy hlarge hx
    exact ⟨hx, hy⟩
  · by_cases hy : y.1 = s
    · right
      right
      have hlargeSwap :
          (((n - 1 : ℕ) : ℝ) * lam) ≤
            EuclideanGeometry.angle (p y.1) (p b) (p x.1) := by
        simpa only [EuclideanGeometry.angle_comm] using hlarge
      have hxa :=
        general_mixed_large_angle_sharp_endpoint_forces_support_one
          hp hcap hn hdelta0 hdeltaHalf ht hlam
          hsa hsb hab Cs Ca Cb hS hA hB hsupA hsupB
          y x hxy.symm hlargeSwap hy
      exact ⟨hxa, hy⟩
    · exact Or.inl ⟨hx, hy⟩

#print axioms general_mixed_large_angle_endpoint_classification

end JSP000404Research
