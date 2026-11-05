import JSP000404Research.OddWireSchedule
import JSP000404Research.PlanarFirstThreshold

/-!
# Unconditional right-angle and two-thirds-pi thresholds

The actual projection curves supply the winding bound for three- and five-phase retiming.
The resulting statements include every finite injective planar configuration.
-/

namespace JSP000404Research

theorem planar_exists_small_odd_rows_of_width {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) {lam width : ℝ}
    (hcap : AngleCap p lam) (hwidth : 0 < width) (hlam : lam = Real.pi / width)
    (q : ℕ) (hq : q = 3 ∨ q = 5 ∨ q = 7) (hbound : width < ((q : ℝ) + 1) / 2)
    (hlarge : 3 ≤ Fintype.card V) :
    ∃ row : V → Fin q → Option Bool, (∀ v, OddWire.PartialValid (row v)) ∧
      ∀ v w, v ≠ w → ∃ c a b, row v c = some a ∧ row w c = some b ∧ a ≠ b := by
  classical
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
  have hdelays := OrderedWires.scaled_wire_delays D hinjective
    (hcardProjection.trans hcard) hm hwidth hbound
  have hcycles := OrderedWires.simple_cycle_winding_of_forward_lift D hinjective
    (hcardProjection.trans hcard) (ProjectionOrdered.genericForwardAngleLift hp)
    hwidth hlampos hscale (fun _ _ ↦ rfl)
  exact WireGraph.exists_partial_rows_of_simple_cycle_winding (V := ProjectionOrdered V) q hq
    (OrderedWires.wire D hinjective (hcardProjection.trans hcard)) OrderedWires.sign
    (fun e ↦ ((((q : ℝ) + 1) / 2) / width) * OrderedWires.value D e)
    (OrderedWires.wire_covers D hinjective (hcardProjection.trans hcard))
    (OrderedWires.wire_pair D hinjective (hcardProjection.trans hcard))
    hdelays.1 hdelays.2 hcycles

theorem planar_card_le_small_period_of_width {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) {lam width : ℝ}
    (hcap : AngleCap p lam) (hwidth : 0 < width) (hlam : lam = Real.pi / width)
    (q : ℕ) (hq : q = 3 ∨ q = 5) (hbound : width < ((q : ℝ) + 1) / 2) :
    Fintype.card V ≤ q := by
  by_cases hsmall : Fintype.card V ≤ 2
  · omega
  obtain ⟨row, hvalid, hsep⟩ := planar_exists_small_odd_rows_of_width hp hcap hwidth hlam
    q (by omega) hbound (by omega)
  exact OddWire.card_le_small_period_of_rows hq row hvalid hsep

/-- Strict caps at pi/2 and 2*pi/3 give capacities three and five. -/
theorem planar_card_le_small_period_of_strict_angles {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) (q : ℕ) (hq : q = 3 ∨ q = 5)
    (hcap : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) <
        Real.pi - Real.pi / (((q : ℝ) + 1) / 2)) : Fintype.card V ≤ q := by
  have hqreal : (3 : ℝ) ≤ q := by exact_mod_cast (show 3 ≤ q by omega)
  have hperiod : 0 < ((q : ℝ) + 1) / 2 := by positivity
  have hthreshold : 0 < Real.pi - Real.pi / (((q : ℝ) + 1) / 2) := by
    have hdiv : Real.pi / (((q : ℝ) + 1) / 2) < Real.pi :=
      (div_lt_iff₀ hperiod).mpr (by nlinarith [Real.pi_pos])
    linarith
  obtain ⟨lam, hstronger, hnewcap⟩ := exists_stronger_angleCap p hthreshold hcap
  have hlampos : 0 < lam := by
    have hdiv := div_pos Real.pi_pos hperiod
    linarith
  have hwidth : 0 < Real.pi / lam := div_pos Real.pi_pos hlampos
  have hbound : Real.pi / lam < ((q : ℝ) + 1) / 2 := by
    apply (div_lt_iff₀ hlampos).mpr
    have h := (div_lt_iff₀ hperiod).mp
      (show Real.pi / (((q : ℝ) + 1) / 2) < lam by linarith)
    nlinarith
  exact planar_card_le_small_period_of_width hp hnewcap hwidth
    (by rw [div_div_cancel₀ Real.pi_ne_zero]) q hq hbound

theorem planar_small_odd_threshold_angle {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) (q : ℕ) (hq : q = 3 ∨ q = 5)
    (hcard : q < Fintype.card V) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Real.pi - Real.pi / (((q : ℝ) + 1) / 2) ≤
        EuclideanGeometry.angle (p a) (p b) (p c) := by
  by_contra! h
  have hcap := planar_card_le_small_period_of_strict_angles hp q hq h
  omega

theorem planar_right_angle {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) (hcard : 3 < Fintype.card V) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Real.pi / 2 ≤ EuclideanGeometry.angle (p a) (p b) (p c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ :=
    planar_small_odd_threshold_angle hp 3 (Or.inl rfl) hcard
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  norm_num at hangle
  linarith

theorem planar_two_thirds_angle {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) (hcard : 5 < Fintype.card V) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      2 * Real.pi / 3 ≤ EuclideanGeometry.angle (p a) (p b) (p c) := by
  obtain ⟨a, b, c, hab, hac, hbc, hangle⟩ :=
    planar_small_odd_threshold_angle hp 5 (Or.inr rfl) hcard
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  norm_num at hangle
  linarith

#print axioms planar_card_le_small_period_of_strict_angles
#print axioms planar_right_angle
#print axioms planar_two_thirds_angle

end JSP000404Research
