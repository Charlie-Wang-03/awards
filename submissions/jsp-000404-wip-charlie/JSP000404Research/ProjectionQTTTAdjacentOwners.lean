import JSP000404Research.ProjectionQTTTAllNSupport
import JSP000404Research.ProjectionLossFlipCoordinate
import Mathlib.Tactic

/-!
# Adjacent owner coordinates in the planar Q/T/T/T terminal

At the completion owner s of a saturated Q/T/T/T state the retained active
palette is exactly {cx,cy,cz}.  Every planar projected-loss vertex contains a
zero-quotient unit-band crossing, hence two adjacent retained active
coordinates.  Therefore one pair among cx,cy,cz is numerically adjacent.
-/

namespace JSP000404Research
namespace ProjectionOrdered

theorem QTTT_completion_owner_coordinates_have_adjacent_pair
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
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
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      let R :=
        standardResidualColoring D n hwidth
      let exponent : ProjectionOrdered V → ℕ :=
        fun q => centreExponent (C q) t
      s ∈ projectedLossVertices R exponent)
    (hsActive :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos hn hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      let R :=
        standardResidualColoring D n hwidth
      retainedActive R s = {cx,cy,cz}) :
    ∃ a b : Fin n,
      a ∈ ({cx,cy,cz} : Finset (Fin n)) ∧
      b ∈ ({cx,cy,cz} : Finset (Fin n)) ∧
      b.val = a.val + 1 := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t :=
    sendov_scale_pos hn hdelta0 ht
  have hwidth : t < (n + 1 : ℕ) := by
    rw [ht]
    exact_mod_cast
      (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let R :=
    standardResidualColoring D n hwidth
  let exponent : ProjectionOrdered V → ℕ :=
    fun q => centreExponent (C q) t

  have hsLoss' : s ∈ projectedLossVertices R exponent := by
    simpa [R,D,exponent] using hsLoss
  have hsActive' :
      retainedActive R s = {cx,cy,cz} := by
    simpa [R,D] using hsActive

  obtain ⟨a,b,hab,hA,hB⟩ :=
    planar_projectedLoss_has_adjacent_retained_active_pair
      hp hcap hn hdelta0 hdeltaHalf ht hlam C s
      (by simpa [R,D,exponent] using hsLoss')

  refine ⟨a,b,?_,?_,hab⟩
  · rw [← hsActive']
    exact hA
  · rw [← hsActive']
    exact hB

#print axioms QTTT_completion_owner_coordinates_have_adjacent_pair

end ProjectionOrdered
end JSP000404Research
