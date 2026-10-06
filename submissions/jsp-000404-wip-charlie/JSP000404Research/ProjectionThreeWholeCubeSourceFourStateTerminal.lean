import JSP000404Research.ThreeWholeCubeSourceExtremePatternReduction
import JSP000404Research.ProjectionThreeWholeCubeSourceExtremeAngles
import JSP000404Research.ProjectionThreeWholeCubeElevenTerminal
import JSP000404Research.SupportOneNarrowCone
import Mathlib.Tactic

/-!
# Ordered-partner four-state terminal for a support-one source

Assume the source v of a saturated three-whole-cube star is the unique
support-one vertex and the three support-two partners are ordered s1<s2<s3.

The general support-two geometry gives an eleven-state small-pair terminal on
(s1,s2,s3;v).  If v is the global minimum, the whole-cube same-band matrix
reduces this to states 1 or 2.  If v is the global maximum, it reduces to
states 6 or 11.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem ordered_threeWholeCube_supportOne_source_four_state_terminal
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
    (hvs1 : v ≠ s₁) (hvs2 : v ≠ s₂) (hvs3 : v ≠ s₃)
    (hs12 : s₁ ≠ s₂) (hs13 : s₁ ≠ s₃) (hs23 : s₂ ≠ s₃)
    (hs12lt : s₁ < s₂)
    (hs23lt : s₂ < s₃)
    {c₁ c₂ c₃ : Fin n}
    (hc12 : c₁ ≠ c₂) (hc13 : c₁ ≠ c₃) (hc23 : c₂ ≠ c₃)
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
    (hvSupport :
      positiveSupport (centreQuotient (Cfam v) t) = 1)
    (hs1Support :
      positiveSupport (centreQuotient (Cfam s₁) t) = 2)
    (hs2Support :
      positiveSupport (centreQuotient (Cfam s₂) t) = 2)
    (hs3Support :
      positiveSupport (centreQuotient (Cfam s₃) t) = 2)
    (hactive :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R v = {c₁,c₂,c₃})
    (h₁ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₁ v c₁)
    (h₂ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₂ v c₂)
    (h₃ :
      letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
      let R := planarStandardResidualColoring
        hp hcap (by omega : 1 ≤ n)
        hdelta0 (by linarith : delta < 1) ht hlam
      WholeCubeQTPair R s₃ v c₃)
    (hextreme :
      (∀ w : ProjectionOrdered V, w ≠ v → v < w) ∨
      (∀ w : ProjectionOrdered V, w ≠ v → w < v)) :
    (
      ThreeSupportTwoCrossedPattern11
        (reindexedPoint p) delta lam s₁ s₂ s₃ v
      ∧
      (
        (
          EuclideanGeometry.angle (reindexedPoint p s₂) (reindexedPoint p s₁) (reindexedPoint p s₃) ≤ delta * lam ∧
          EuclideanGeometry.angle (reindexedPoint p s₁) (reindexedPoint p s₂) (reindexedPoint p v) ≤ delta * lam ∧
          EuclideanGeometry.angle (reindexedPoint p s₁) (reindexedPoint p s₃) (reindexedPoint p v) ≤ delta * lam
        )
        ∨
        (
          EuclideanGeometry.angle (reindexedPoint p s₂) (reindexedPoint p s₁) (reindexedPoint p s₃) ≤ delta * lam ∧
          EuclideanGeometry.angle (reindexedPoint p s₁) (reindexedPoint p s₂) (reindexedPoint p v) ≤ delta * lam ∧
          EuclideanGeometry.angle (reindexedPoint p s₂) (reindexedPoint p s₃) (reindexedPoint p v) ≤ delta * lam
        )
      )
    )
    ∨
    (
      ThreeSupportTwoCrossedPattern11
        (reindexedPoint p) delta lam s₁ s₂ s₃ v
      ∧
      (
        (
          EuclideanGeometry.angle (reindexedPoint p s₂) (reindexedPoint p s₁) (reindexedPoint p v) ≤ delta * lam ∧
          EuclideanGeometry.angle (reindexedPoint p s₃) (reindexedPoint p s₂) (reindexedPoint p v) ≤ delta * lam ∧
          EuclideanGeometry.angle (reindexedPoint p s₁) (reindexedPoint p s₃) (reindexedPoint p s₂) ≤ delta * lam
        )
        ∨
        (
          EuclideanGeometry.angle (reindexedPoint p s₃) (reindexedPoint p s₁) (reindexedPoint p v) ≤ delta * lam ∧
          EuclideanGeometry.angle (reindexedPoint p s₃) (reindexedPoint p s₂) (reindexedPoint p v) ≤ delta * lam ∧
          EuclideanGeometry.angle (reindexedPoint p s₁) (reindexedPoint p s₃) (reindexedPoint p s₂) ≤ delta * lam
        )
      )
    ) := by
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have hn1 : 1 ≤ n := by omega
  have hdelta1 : delta < 1 := by linarith

  have hpat :=
    three_supportTwo_secondLayer_four_reduce_to_eleven
      (reindexedPoint_injective hp)
      (by
        intro a b c hab hac hbc
        exact hcap a.toOriginal b.toOriginal c.toOriginal
          (by intro h; apply hab; exact toOriginal_injective h)
          (by intro h; apply hac; exact toOriginal_injective h)
          (by intro h; apply hbc; exact toOriginal_injective h))
      (by omega : 3 ≤ n) hdelta0 hdeltaHalf ht hlam
      hs12 hs13 hvs1.symm hs23 hvs2.symm hvs3.symm
      Cfam hs1Second hs2Second hs3Second
      hs1Support hs2Support hs3Support

  let Hv :=
    Classical.choice
      (exists_highExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp)
        (by
          intro a b c hab hac hbc
          exact hcap a.toOriginal b.toOriginal c.toOriginal
            (by intro h; apply hab; exact toOriginal_injective h)
            (by intro h; apply hac; exact toOriginal_injective h)
            (by intro h; apply hbc; exact toOriginal_injective h))
        hn1 hdelta0 hdelta1 ht hlam
        v (Cfam v) (by rw [hvSecond]; omega))

  have hcone
      {x y : ProjectionOrdered V}
      (hxv : x ≠ v) (hyv : y ≠ v) :
      EuclideanGeometry.angle
        (reindexedPoint p x) (reindexedPoint p v) (reindexedPoint p y)
        ≤ (1 + delta) * lam := by
    exact secondLayer_supportOne_all_angles_le_one_add_delta_lam
      (reindexedPoint_injective hp)
      (by omega : 3 ≤ n) hdelta0 ht hlam
      (Cfam v) hvSecond hvSupport Hv hxv hyv

  rcases hextreme with hmin | hmax
  · have hang :=
      threeWholeCube_source_globalMin_sameBand_angles
        hp hcap Cfam hn1 hdelta0 hdelta1 ht hlam
        hvs1 hvs2 hvs3 hs12 hs13 hs23
        hc12 hc13 hc23
        hvLoss
        (by rw [hactive]; simp)
        (by rw [hactive]; simp)
        (by rw [hactive]; simp)
        h₁ h₂ h₃ hmin hs12lt hs23lt
    have hred :=
      threeSupport_eleven_reduce_to_one_or_two_of_sourceMin_angles
        (reindexedPoint_injective hp)
        hn4 hdelta0 hdeltaHalf ht hlam
        hs12 hs13 hvs1.symm hs23 hvs2.symm hvs3.symm
        hpat
        (by simpa [EuclideanGeometry.angle_comm] using hang.2.2.2)
        hang.2.1
        hang.1
        hang.2.2.1
        (hcone hvs1 hvs2)
        (hcone hvs1 hvs3)
        (hcone hvs2 hvs3)
    exact Or.inl ⟨hpat,hred⟩
  · have hang :=
      threeWholeCube_source_globalMax_sameBand_angles
        hp hcap Cfam hn1 hdelta0 hdelta1 ht hlam
        hvs1 hvs2 hvs3 hs12 hs13 hs23
        hc12 hc13 hc23
        hvLoss
        (by rw [hactive]; simp)
        (by rw [hactive]; simp)
        (by rw [hactive]; simp)
        h₁ h₂ h₃ hmax hs12lt hs23lt
    have hred :=
      threeSupport_eleven_reduce_to_six_or_eleven_of_sourceMax_angles
        (reindexedPoint_injective hp)
        hn4 hdelta0 hdeltaHalf ht hlam
        hs12 hs13 hvs1.symm hs23 hvs2.symm hvs3.symm
        hpat
        hang.1 hang.2.1 hang.2.2.1 hang.2.2.2
        (hcone hvs1 hvs2)
        (hcone hvs1 hvs3)
        (hcone hvs2 hvs3)
    exact Or.inr ⟨hpat,hred⟩

#print axioms ordered_threeWholeCube_supportOne_source_four_state_terminal

end ProjectionOrdered
end JSP000404Research
