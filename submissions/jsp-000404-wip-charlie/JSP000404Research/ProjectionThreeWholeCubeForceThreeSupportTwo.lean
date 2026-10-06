import JSP000404Research.ProjectionThreeWholeCubeNoTwoSupportOne
import JSP000404Research.ThreeWholeCubeSupportTerminal
import Mathlib.Tactic

/-!
# At least three support-two centres in the saturated whole-cube terminal

The generic four-second-layer support dichotomy says:
* at least three support-two centres; or
* exactly two support-two and two support-one centres.

For n>=4 the second alternative is impossible in a saturated
three-whole-cube code star, because no two distinct vertices in the star can
both be support-one.

Hence the saturated four-vertex terminal always contains three distinct
support-two centres.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem planar_threeWholeCubePartners_force_three_supportTwo
    {V : Type*} [Fintype V]
    {p : V → Plane}
    {lam t delta : ℝ} {n : ℕ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    {v s₁ s₂ s₃ : ProjectionOrdered V}
    (hvs1 : v ≠ s₁)
    (hvs2 : v ≠ s₂)
    (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂)
    (hs13 : s₁ ≠ s₃)
    (hs23 : s₂ ≠ s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂)
    (hc13 : c₁ ≠ c₃)
    (hc23 : c₂ ≠ c₃)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {c₁,c₂,c₃})
    (hvLoss :
      v ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs1Loss :
      s₁ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs2Loss :
      s₂ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hs3Loss :
      s₃ ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hvSecond : centreExponent (Cfam v) t = n - 2)
    (hs1Second : centreExponent (Cfam s₁) t = n - 2)
    (hs2Second : centreExponent (Cfam s₂) t = n - 2)
    (hs3Second : centreExponent (Cfam s₃) t = n - 2)
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₁ v c₁)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₂ v c₂)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₃ v c₃) :
    ∃ a b c : ProjectionOrdered V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      b ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      c ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      positiveSupport (centreQuotient (Cfam a) t) = 2 ∧
      positiveSupport (centreQuotient (Cfam b) t) = 2 ∧
      positiveSupport (centreQuotient (Cfam c) t) = 2 := by
  have hterm :=
    threeWholeCube_four_vertex_support_terminal
      (reindexedPoint_injective hp)
      (by
        intro a b c hab hac hbc
        exact hcap a.toOriginal b.toOriginal c.toOriginal
          (by
            intro h
            apply hab
            exact ProjectionOrdered.toOriginal_injective h)
          (by
            intro h
            apply hac
            exact ProjectionOrdered.toOriginal_injective h)
          (by
            intro h
            apply hbc
            exact ProjectionOrdered.toOriginal_injective h))
      (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam
      hvs1 hvs2 hvs3 hs12 hs13 hs23
      hvSecond hs1Second hs2Second hs3Second

  rcases hterm with hthree | hexact
  · exact hthree
  · obtain ⟨u₁,u₂,o₁,o₂,
      hu12,hu1o1,hu1o2,hu2o1,hu2o2,ho12,
      hu1Mem,hu2Mem,ho1Mem,ho2Mem,
      hu1Support,hu2Support,ho1Support,ho2Support,
      _cert1,_cert2,_hq1,_hq2,_hidden1,_hidden2⟩ := hexact
    exact False.elim
      (planar_threeWholeCubePartners_no_two_supportOne
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
        hc12 hc13 hc23 hactive
        hvLoss hs1Loss hs2Loss hs3Loss
        hvSecond hs1Second hs2Second hs3Second
        h₁ h₂ h₃
        ho1Mem ho2Mem ho12
        ho1Support ho2Support)

#print axioms planar_threeWholeCubePartners_force_three_supportTwo

end ProjectionOrdered
end JSP000404Research
