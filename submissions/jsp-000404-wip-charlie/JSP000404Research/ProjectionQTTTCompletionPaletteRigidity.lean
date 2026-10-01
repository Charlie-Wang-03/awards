import JSP000404Research.ProjectionUnitSupportTwoConsecutiveBands
import Mathlib.Tactic

/-!
# Consecutive owner coordinates at a unit-transition Q/T/T/T completion owner
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem QTTT_unitSupportTwo_completion_owner_coordinates_consecutive
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
    {s : ProjectionOrdered V}
    {cx cy cz : Fin n}
    (hsLoss :
      s ∈ projectedLossVertices
        (planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam)
        (planarCentreExponent hp C))
    (hsSecond : centreExponent (C s) t = n - 2)
    (hsSupport :
      positiveSupport (centreQuotient (C s) t) = 2)
    (cert :
      HighExponentTransitionIntervalCertificate
        (reindexedPoint_injective hp) t s (C s))
    (hqe : cert.qe = 1)
    (hsActive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let R :=
        planarStandardResidualColoring
          hp hcap (by omega : 1 ≤ n)
          hdelta0 (by linarith : delta < 1) ht hlam
      retainedActive R s = {cx,cy,cz}) :
    ∃ m : ℕ,
      ({cx.val,cy.val,cz.val} : Finset ℕ) =
        {m,m+1,m+2} := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  let R :=
    planarStandardResidualColoring
      hp hcap (by omega : 1 ≤ n)
      hdelta0 (by linarith : delta < 1) ht hlam

  obtain ⟨m,hm⟩ :=
    planar_projectedLoss_unitSupportTwo_retainedPalette_consecutive
      hp hcap hn3 hdelta0 hdeltaHalf ht hlam
      C s hsLoss hsSecond hsSupport cert hqe

  have hsActive' :
      retainedActive R s = {cx,cy,cz} := by
    simpa [R] using hsActive

  refine ⟨m,?_⟩
  have hm' :
      (retainedActive R s).map Fin.valEmbedding =
        {m,m+1,m+2} := by
    simpa [R] using hm
  rw [hsActive'] at hm'
  simpa using hm'

#print axioms QTTT_unitSupportTwo_completion_owner_coordinates_consecutive

end ProjectionOrdered
end JSP000404Research
