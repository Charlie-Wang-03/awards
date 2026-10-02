import JSP000404Research.ResidualThreeWholeCubeMinimalCoreCollapse
import JSP000404Research.SecondLayerFourSupportTerminal
import Mathlib.Tactic

/-!
# Support terminal for the saturated three-whole-cube four-vertex core

The finite-state whole-cube recursion ends at four second-layer projected-loss
vertices

  v, s1, s2, s3

where v has one WholeCubeQTPair partner at each of its three active
coordinates.

Independently, every four distinct second-layer centres satisfy the uniform
support dichotomy:

* at least three are support-two; or
* exactly two are support-two and two support-one, with both support-two
  transition quotients equal to one and hidden n-1 quotients.

This file connects those two previously separate terminal surfaces.
-/

namespace JSP000404Research

theorem threeWholeCube_four_vertex_support_terminal
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ q : V, CentreProjectiveCycle hp q)
    {v s₁ s₂ s₃ : V}
    (hvs1 : v ≠ s₁)
    (hvs2 : v ≠ s₂)
    (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂)
    (hs13 : s₁ ≠ s₃)
    (hs23 : s₂ ≠ s₃)
    (hvSecond : centreExponent (C v) t = n - 2)
    (hs1Second : centreExponent (C s₁) t = n - 2)
    (hs2Second : centreExponent (C s₂) t = n - 2)
    (hs3Second : centreExponent (C s₃) t = n - 2) :
    FourSecondLayerSupportTerminal hp t n C v s₁ s₂ s₃ := by
  exact four_secondLayer_support_terminal
    hp hcap hn3 hdelta0 hdeltaHalf ht hlam C
    hvs1 hvs2 hvs3 hs12 hs13 hs23
    hvSecond hs1Second hs2Second hs3Second

#print axioms threeWholeCube_four_vertex_support_terminal

end JSP000404Research
