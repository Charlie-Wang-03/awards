import JSP000404Research.PlanarSmallOddThresholds
import JSP000404Research.SevenPhaseCapacity

/-!
# The unconditional three-quarters-pi threshold

The seven-phase fractional covering certificate applies to the actual projection-wire
retiming. A strict cap at 3*pi/4 therefore allows at most ten ordinary planar points.
-/

namespace JSP000404Research

theorem planar_card_le_ten_of_width {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) {lam width : ℝ}
    (hcap : AngleCap p lam) (hwidth : 0 < width) (hlam : lam = Real.pi / width)
    (hbound : width < 4) : Fintype.card V ≤ 10 := by
  by_cases hsmall : Fintype.card V ≤ 2
  · omega
  obtain ⟨row, hvalid, hsep⟩ := planar_exists_small_odd_rows_of_width hp hcap hwidth hlam
    7 (Or.inr (Or.inr rfl)) (by norm_num; exact hbound) (by omega)
  exact OddWire.card_le_ten_of_seven_rows row hvalid hsep

/-- Family B at n=3, with all ordinary planar configurations included. -/
theorem planar_card_le_ten_of_strict_angles {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p)
    (hcap : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) < 3 * Real.pi / 4) :
    Fintype.card V ≤ 10 := by
  obtain ⟨lam, hstronger, hnewcap⟩ := exists_stronger_angleCap p (by positivity) hcap
  have hlampos : 0 < lam := by nlinarith [Real.pi_pos]
  have hwidth : 0 < Real.pi / lam := div_pos Real.pi_pos hlampos
  have hbound : Real.pi / lam < 4 := (div_lt_iff₀ hlampos).mpr (by linarith)
  exact planar_card_le_ten_of_width hp hnewcap hwidth
    (by rw [div_div_cancel₀ Real.pi_ne_zero]) hbound

theorem planar_three_quarters_angle {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) (hcard : 10 < Fintype.card V) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      3 * Real.pi / 4 ≤ EuclideanGeometry.angle (p a) (p b) (p c) := by
  by_contra! h
  have hcap := planar_card_le_ten_of_strict_angles hp h
  omega

#print axioms planar_card_le_ten_of_strict_angles
#print axioms planar_three_quarters_angle

end JSP000404Research
