import JSP000404Research.ProjectionThreeWholeCubeNoTwoSupportOne
import JSP000404Research.ProjectionSupportOneConsecutivePalette
import JSP000404Research.ProjectionSupportOneGlobalExtreme
import JSP000404Research.ThreeWholeCubeRetainedCodeStar
import Mathlib.Tactic

/-!
# Sharp support terminal for the saturated three-whole-cube star

For n >= 4 every vertex of the saturated four-vertex whole-cube star is a
second-layer centre, hence has positive quotient support one or two.

No two distinct star vertices can both be support-one.  Therefore exactly one
of the following holds:

* all four vertices are support-two; or
* there is a unique support-one vertex o, every other star vertex is
  support-two, o is a global projection-order extreme, and the common retained
  palette of all four vertices is a consecutive triple.

This is a sharper terminal than merely "at least three support-two".
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCubePartners_sharp_support_terminal
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
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
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let R :=
      planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
    (
      ∀ q : ProjectionOrdered V,
        q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
        positiveSupport (centreQuotient (Cfam q) t) = 2
    )
    ∨
    ∃ o : ProjectionOrdered V,
      o ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) ∧
      positiveSupport (centreQuotient (Cfam o) t) = 1 ∧
      GlobalOrderExtreme o ∧
      (∀ q : ProjectionOrdered V,
        q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
        q ≠ o →
        positiveSupport (centreQuotient (Cfam q) t) = 2) ∧
      ∃ m : ℕ,
        (retainedActive R v).map Fin.valEmbedding = threeNatInterval m ∧
        (retainedActive R s₁).map Fin.valEmbedding = threeNatInterval m ∧
        (retainedActive R s₂).map Fin.valEmbedding = threeNatInterval m ∧
        (retainedActive R s₃).map Fin.valEmbedding = threeNatInterval m := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam
  let exponent := planarCentreExponent hp Cfam
  let S : Finset (ProjectionOrdered V) := {v,s₁,s₂,s₃}

  have loss_of_mem :
      ∀ {q : ProjectionOrdered V}, q ∈ S →
        q ∈ projectedLossVertices R exponent := by
    intro q hq
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simpa [R,exponent] using hvLoss
    · simpa [R,exponent] using hs1Loss
    · simpa [R,exponent] using hs2Loss
    · simpa [R,exponent] using hs3Loss

  have second_of_mem :
      ∀ {q : ProjectionOrdered V}, q ∈ S →
        centreExponent (Cfam q) t = n - 2 := by
    intro q hq
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvSecond
    · exact hs1Second
    · exact hs2Second
    · exact hs3Second

  have support_one_or_two :
      ∀ {q : ProjectionOrdered V}, q ∈ S →
        positiveSupport (centreQuotient (Cfam q) t) = 1 ∨
        positiveSupport (centreQuotient (Cfam q) t) = 2 := by
    intro q hq
    exact deficit_two_support_one_or_two_concrete
      (Cfam q) (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht (second_of_mem hq)

  by_cases hall :
      ∀ q : ProjectionOrdered V, q ∈ S →
        positiveSupport (centreQuotient (Cfam q) t) = 2
  · exact Or.inl (by simpa [S,R] using hall)

  · right
    push_neg at hall
    obtain ⟨o,hoS,hoNotTwo⟩ := hall
    have hoClass := support_one_or_two hoS
    have hoOne :
        positiveSupport (centreQuotient (Cfam o) t) = 1 :=
      hoClass.resolve_right hoNotTwo

    have hothers :
        ∀ q : ProjectionOrdered V, q ∈ S → q ≠ o →
          positiveSupport (centreQuotient (Cfam q) t) = 2 := by
      intro q hq hqo
      rcases support_one_or_two hq with hqOne | hqTwo
      · exact False.elim
          (planar_threeWholeCubePartners_no_two_supportOne
            hp hcap hn4 hdelta0 hdeltaHalf ht hlam Cfam
            hc12 hc13 hc23 hactive
            hvLoss hs1Loss hs2Loss hs3Loss
            hvSecond hs1Second hs2Second hs3Second
            h₁ h₂ h₃
            hoS hq hqo.symm
            hoOne hqOne)
      · exact hqTwo

    have hdelta1 : delta < 1 := by linarith
    let Ho :=
      Classical.choice
        (exists_highExponentTransitionIntervalCertificate
          (reindexedPoint_injective hp) hcap
          (by omega : 1 ≤ n)
          hdelta0 hdelta1 ht hlam
          o (Cfam o)
          (by rw [second_of_mem hoS]; omega))

    have hoExtreme :
        GlobalOrderExtreme o :=
      planar_projectedLoss_secondLayer_supportOne_globalExtreme
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        Cfam o
        (by simpa [R,exponent] using loss_of_mem hoS)
        (second_of_mem hoS) hoOne Ho

    have hc1V : c₁ ∈ retainedActive R v := by
      rw [hactive]
      simp
    have hc2V : c₂ ∈ retainedActive R v := by
      rw [hactive]
      simp
    have hc3V : c₃ ∈ retainedActive R v := by
      rw [hactive]
      simp

    have hstar1 :=
      wholeCube_retainedCode_single_flip
        R hc1V (by simpa [R] using h₁)
    have hstar2 :=
      wholeCube_retainedCode_single_flip
        R hc2V (by simpa [R] using h₂)
    have hstar3 :=
      wholeCube_retainedCode_single_flip
        R hc3V (by simpa [R] using h₃)

    have palette_eq_v :
        ∀ {q : ProjectionOrdered V}, q ∈ S →
          retainedActive R q = retainedActive R v := by
      intro q hq
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · rfl
      · exact hstar1.1
      · exact hstar2.1
      · exact hstar3.1

    obtain ⟨m,hpalO⟩ :=
      planar_projectedLoss_supportOne_retainedPalette_consecutive
        hp hcap (by omega : 3 ≤ n)
        hdelta0 hdeltaHalf ht hlam
        Cfam o
        (by simpa [R,exponent] using loss_of_mem hoS)
        (second_of_mem hoS) hoOne

    have hpalV :
        (retainedActive R v).map Fin.valEmbedding =
          threeNatInterval m := by
      rw [← palette_eq_v hoS]
      simpa [R,threeNatInterval] using hpalO

    have hpalS1 :
        (retainedActive R s₁).map Fin.valEmbedding =
          threeNatInterval m := by
      rw [hstar1.1]
      exact hpalV
    have hpalS2 :
        (retainedActive R s₂).map Fin.valEmbedding =
          threeNatInterval m := by
      rw [hstar2.1]
      exact hpalV
    have hpalS3 :
        (retainedActive R s₃).map Fin.valEmbedding =
          threeNatInterval m := by
      rw [hstar3.1]
      exact hpalV

    exact ⟨o,by simpa [S],hoOne,hoExtreme,
      (by
        intro q hq hqo
        exact hothers q (by simpa [S] using hq) hqo),
      m,hpalV,hpalS1,hpalS2,hpalS3⟩

#print axioms planar_threeWholeCubePartners_sharp_support_terminal

end ProjectionOrdered
end JSP000404Research
