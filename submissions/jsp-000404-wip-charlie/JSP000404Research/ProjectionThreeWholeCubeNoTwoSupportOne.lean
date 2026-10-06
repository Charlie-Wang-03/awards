import JSP000404Research.ThreeWholeCubeExtremeUniqueness
import JSP000404Research.ProjectionSupportOneGlobalExtreme
import JSP000404Research.ThreeWholeCubeSupportTerminal
import Mathlib.Tactic

/-!
# No two support-one vertices in the saturated three-whole-cube terminal

For n >= 4, every planar projected-loss second-layer support-one centre is a
global order extreme.  Every global extreme projected-loss vertex has a
constant retained code.  But the retained-code star consisting of a source
and its three whole-cube partners contains at most one constant code.

Therefore among the four saturated whole-cube vertices, no two distinct
vertices can both be support-one.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCubePartners_no_two_supportOne
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
      WholeCubeQTPair R s₃ v c₃)
    {a b : ProjectionOrdered V}
    (haMem : a ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)))
    (hbMem : b ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)))
    (hab : a ≠ b)
    (haSupport :
      positiveSupport (centreQuotient (Cfam a) t) = 1)
    (hbSupport :
      positiveSupport (centreQuotient (Cfam b) t) = 1) :
    False := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam
  let exponent := planarCentreExponent hp Cfam

  have loss_of_mem :
      ∀ {q : ProjectionOrdered V},
        q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
        q ∈ projectedLossVertices R exponent := by
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simpa [R,exponent] using hvLoss
    · simpa [R,exponent] using hs1Loss
    · simpa [R,exponent] using hs2Loss
    · simpa [R,exponent] using hs3Loss

  have second_of_mem :
      ∀ {q : ProjectionOrdered V},
        q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
        centreExponent (Cfam q) t = n - 2 := by
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvSecond
    · exact hs1Second
    · exact hs2Second
    · exact hs3Second

  have haLoss := loss_of_mem haMem
  have hbLoss := loss_of_mem hbMem
  have haSecond := second_of_mem haMem
  have hbSecond := second_of_mem hbMem

  have hdelta1 : delta < 1 := by linarith
  let Ha :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) hcap
        (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        a (Cfam a) (by rw [haSecond]; omega))
  let Hb :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) hcap
        (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        b (Cfam b) (by rw [hbSecond]; omega))

  have haExtreme :
      GlobalOrderExtreme a :=
    planar_projectedLoss_secondLayer_supportOne_globalExtreme
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      Cfam a
      (by simpa [R,exponent] using haLoss)
      haSecond haSupport Ha
  have hbExtreme :
      GlobalOrderExtreme b :=
    planar_projectedLoss_secondLayer_supportOne_globalExtreme
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      Cfam b
      (by simpa [R,exponent] using hbLoss)
      hbSecond hbSupport Hb

  have haConst :
      ConstantRetainedCode R a :=
    projectedLoss_globalExtreme_constantCode
      R exponent haLoss haExtreme
  have hbConst :
      ConstantRetainedCode R b :=
    projectedLoss_globalExtreme_constantCode
      R exponent hbLoss hbExtreme

  have huniq :=
    threeWholeCubePartners_at_most_one_constantCode
      R
      hc12 hc13 hc23
      (by simpa [R] using hactive)
      (by simpa [R] using h₁)
      (by simpa [R] using h₂)
      (by simpa [R] using h₃)

  exact huniq a b haMem hbMem hab ⟨haConst,hbConst⟩

#print axioms planar_threeWholeCubePartners_no_two_supportOne

end ProjectionOrdered
end JSP000404Research
