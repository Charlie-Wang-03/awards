import JSP000404Research.LargeTransitionNarrowCone
import JSP000404Research.ProjectionConsecutiveSupportTwoTransitionDichotomy
import Mathlib.Tactic

/-!
# Projection-facing unit-or-narrow dichotomy

At a planar projected-loss second-layer support-two centre with a consecutive
three-band retained palette, every high-exponent transition certificate has
qe=1 or qe=n-1.

The n-1 branch is globally narrow: every angle between two rays from the
centre is at most (1+delta)*lambda.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring

theorem planar_supportTwo_consecutivePalette_unit_or_narrow
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n m : ℕ}
    (hn3 : 3 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (Cfam :
      ∀ q : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) q)
    (i : ProjectionOrdered V)
    (hloss :
      i ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp Cfam))
    (hsecond :
      centreExponent (Cfam i) t = n - 2)
    (hsupport :
      positiveSupport (centreQuotient (Cfam i) t) = 2)
    (hpalette :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      (retainedActive R i).map Fin.valEmbedding =
        threeNatInterval m)
    (H :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t i (Cfam i)) :
    H.qe = 1 ∨
    (∀ {j k : ProjectionOrdered V},
      j ≠ i → k ≠ i →
      EuclideanGeometry.angle
        (reindexedPoint p j) (reindexedPoint p i) (reindexedPoint p k)
        ≤ (1 + delta) * lam) := by
  have hdich :=
    planar_projectedLoss_supportTwo_consecutivePalette_transition_qe_dichotomy
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      Cfam i hloss hsecond hsupport hpalette H
  rcases hdich with h1 | hN
  · exact Or.inl h1
  · right
    intro j k hji hki
    exact transition_n_sub_one_all_angles_le_one_add_delta_lam
      (reindexedPoint_injective hp)
      hn3 hdelta0 ht hlam
      (Cfam i) H hN hji hki

#print axioms planar_supportTwo_consecutivePalette_unit_or_narrow

end ProjectionOrdered
end JSP000404Research
