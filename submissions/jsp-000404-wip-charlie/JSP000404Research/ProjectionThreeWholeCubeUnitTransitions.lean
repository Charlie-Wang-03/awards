import JSP000404Research.ProjectionLargeTransitionGlobalExtreme
import JSP000404Research.ProjectionConsecutiveSupportTwoTransitionDichotomy
import JSP000404Research.ThreeWholeCubeExtremeUniqueness
import Mathlib.Tactic

/-!
# Unique-support-one saturated star forces unit transitions elsewhere

Consider the saturated three-whole-cube star

  {v,s1,s2,s3}

in the n>=4 lower branch.  Suppose o is its unique support-one centre, hence a
global order extreme, while the other three vertices are support-two.  The
whole-cube star shares one consecutive retained palette across all four
vertices.

For any support-two member q, the consecutive-palette transition dichotomy
gives

  H.qe = 1 or H.qe = n-1.

If H.qe=n-1, the large-transition narrow-cone theorem plus the same consecutive
palette forces q to be a global order extreme.  Both o and q would then have
constant retained codes.  But a three-coordinate whole-cube code star contains
at most one constant code.  Contradiction.

Therefore every support-two member has a high-exponent transition certificate
with quotient exactly one.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_threeWholeCube_uniqueSupportOne_others_unitTransition
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
    {v s₁ s₂ s₃ o : ProjectionOrdered V}
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
      WholeCubeQTPair R s₃ v c₃)
    (hoMem :
      o ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)))
    (hoExtreme :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      GlobalOrderExtreme o)
    (hothers :
      ∀ q : ProjectionOrdered V,
        q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
        q ≠ o →
        positiveSupport (centreQuotient (Cfam q) t) = 2)
    {m : ℕ}
    (hpalV :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R v).map Fin.valEmbedding = threeNatInterval m)
    (hpalS1 :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R s₁).map Fin.valEmbedding = threeNatInterval m)
    (hpalS2 :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R s₂).map Fin.valEmbedding = threeNatInterval m)
    (hpalS3 :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R s₃).map Fin.valEmbedding = threeNatInterval m) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    ∀ q : ProjectionOrdered V,
      q ∈ ({v,s₁,s₂,s₃} : Finset (ProjectionOrdered V)) →
      q ≠ o →
      ∃ H : HighExponentTransitionIntervalCertificate
          (reindexedPoint_injective hp) t q (Cfam q),
        H.qe = 1 := by
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

  have palette_of_mem :
      ∀ {q : ProjectionOrdered V}, q ∈ S →
        (retainedActive R q).map Fin.valEmbedding =
          threeNatInterval m := by
    intro q hq
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · simpa [R] using hpalV
    · simpa [R] using hpalS1
    · simpa [R] using hpalS2
    · simpa [R] using hpalS3

  have hoLoss : o ∈ projectedLossVertices R exponent :=
    loss_of_mem (by simpa [S] using hoMem)
  have hoConst :
      ConstantRetainedCode R o :=
    projectedLoss_globalExtreme_constantCode
      R exponent hoLoss (by simpa [GlobalOrderExtreme] using hoExtreme)

  intro q hq hqo
  have hqS : q ∈ S := by simpa [S] using hq
  have hqSupport :
      positiveSupport (centreQuotient (Cfam q) t) = 2 :=
    hothers q hq hqo
  have hdelta1 : delta < 1 := by linarith
  let H :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) hcap
        (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam
        q (Cfam q)
        (by rw [second_of_mem hqS]; omega))

  have hDich :
      H.qe = 1 ∨ H.qe = n - 1 :=
    planar_projectedLoss_supportTwo_consecutivePalette_transition_qe_dichotomy
      hp hcap (by omega : 3 ≤ n)
      hdelta0 hdeltaHalf ht hlam Cfam q
      (by simpa [R,exponent] using loss_of_mem hqS)
      (second_of_mem hqS) hqSupport
      (by simpa [R] using palette_of_mem hqS)
      H

  rcases hDich with hOne | hLarge
  · exact ⟨H,hOne⟩
  · have hqExtreme :
        GlobalOrderExtreme q :=
      planar_projectedLoss_consecutivePalette_transition_n_sub_one_globalExtreme
        hp hcap hn4 hdelta0 hdeltaHalf ht hlam
        Cfam q
        (by simpa [R,exponent] using loss_of_mem hqS)
        (by simpa [R] using palette_of_mem hqS)
        H hLarge
    have hqConst :
        ConstantRetainedCode R q :=
      projectedLoss_globalExtreme_constantCode
        R exponent (loss_of_mem hqS)
        (by simpa [GlobalOrderExtreme] using hqExtreme)
    exact False.elim
      (threeWholeCubePartners_at_most_one_constantCode
        R hc12 hc13 hc23
        (by simpa [R] using hactive)
        (by simpa [R] using h₁)
        (by simpa [R] using h₂)
        (by simpa [R] using h₃)
        o q
        (by simpa [S] using hoMem)
        (by simpa [S] using hq)
        hqo
        ⟨hoConst,hqConst⟩)

#print axioms planar_threeWholeCube_uniqueSupportOne_others_unitTransition

end ProjectionOrdered
end JSP000404Research
