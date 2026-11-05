import JSP000404Research.OrderedElevenPhase
import JSP000404Research.PlanarFirstThreshold

/-!
# The unconditional five-sixths-pi threshold

The actual projection wires retain triple coherence after eleven-phase retiming. Their
verified finite capacity is forty, for every ordinary finite injective planar set.
-/

namespace JSP000404Research

theorem planar_card_le_forty_of_width {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) {lam width : ℝ}
    (hcap : AngleCap p lam) (hwidth : 0 < width) (hlam : lam = Real.pi / width)
    (hbound : width < 6) : Fintype.card V ≤ 40 := by
  classical
  by_cases hsmall : Fintype.card V ≤ 2
  · omega
  have hlarge : 3 ≤ Fintype.card V := by omega
  let m := Fintype.card V - 2
  have hm : 0 < m := by dsimp [m]; omega
  have hcard : Fintype.card V = m + 2 := by dsimp [m]; omega
  let := ProjectionOrdered.projectionLinearOrder hp
  let D := ProjectionOrdered.genericDirectionData_sendov hp hcap hwidth hlam
  have hinjective : ∀ v, Function.Injective (D.localDirectionValue v) :=
    ProjectionOrdered.generic_localDirectionValue_injective hp hcap hwidth hlam
  have hcardProjection : Fintype.card (ProjectionOrdered V) = Fintype.card V :=
    Fintype.card_congr (show ProjectionOrdered V ≃ V from Equiv.refl V)
  have hlampos : 0 < lam := by rw [hlam]; exact div_pos Real.pi_pos hwidth
  have hscale : lam * width = Real.pi := by rw [hlam]; exact div_mul_cancel₀ _ hwidth.ne'
  have hcycles := OrderedWires.simple_cycle_winding_of_forward_lift D hinjective
    (hcardProjection.trans hcard) (ProjectionOrdered.genericForwardAngleLift hp)
    hwidth hlampos hscale (fun _ _ ↦ rfl)
  have h := OrderedWires.card_le_forty_of_winding D hinjective
    (hcardProjection.trans hcard) hm hwidth hbound hcycles
  simpa only [hcardProjection] using h

/-- Family B at n=5 includes all ordinary finite planar configurations. -/
theorem planar_card_le_forty_of_strict_angles {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) < 5 * Real.pi / 6) :
    Fintype.card V ≤ 40 := by
  obtain ⟨lam, hstronger, hnewcap⟩ := exists_stronger_angleCap p (by positivity) hcap
  have hlampos : 0 < lam := by nlinarith [Real.pi_pos]
  have hwidth : 0 < Real.pi / lam := div_pos Real.pi_pos hlampos
  have hbound : Real.pi / lam < 6 := (div_lt_iff₀ hlampos).mpr (by linarith)
  exact planar_card_le_forty_of_width hp hnewcap hwidth
    (by rw [div_div_cancel₀ Real.pi_ne_zero]) hbound

theorem planar_five_sixths_angle {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) (hcard : 40 < Fintype.card V) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      5 * Real.pi / 6 ≤ EuclideanGeometry.angle (p a) (p b) (p c) := by
  by_contra! h
  have hcap := planar_card_le_forty_of_strict_angles hp h
  omega

#print axioms planar_card_le_forty_of_strict_angles
#print axioms planar_five_sixths_angle

end JSP000404Research
