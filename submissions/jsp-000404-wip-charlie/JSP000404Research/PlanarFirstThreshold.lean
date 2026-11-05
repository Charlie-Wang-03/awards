import JSP000404Research.OrderedDirectionCurves
import JSP000404Research.ProjectionStrictWireDirections

/-!
# The first unconditional planar cardinality threshold

The rotating projection graph, its simple-cycle winding bound, integral retiming, and
signed-band packing give the first complete threshold family. The statements quantify over
all finite injective planar configurations. Strict finite caps provide the required slack.
-/

namespace JSP000404Research

theorem planar_card_le_two_pow_of_width {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) {lam width : ℝ}
    (hcap : AngleCap p lam) (hwidth : 0 < width) (hlam : lam = Real.pi / width)
    (n : ℕ) (hn : 0 < n) (hbound : width < (n : ℝ) + 1 / 2) :
    Fintype.card V ≤ 2 ^ n := by
  classical
  by_cases hsmall : Fintype.card V ≤ 2
  · apply hsmall.trans
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn
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
  have h := OrderedWires.card_le_two_pow_of_forward_lift D hinjective
    (hcardProjection.trans hcard) (ProjectionOrdered.genericForwardAngleLift hp)
    hwidth hlampos hscale (fun _ _ ↦ rfl) hm n hn hbound
  simpa only [hcardProjection] using h

/-- A finite strict angle cap can be tightened to a non-strict cap. -/
theorem exists_stronger_angleCap {V : Type*} [Fintype V] (p : V → Plane)
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hcap : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) < threshold) :
    ∃ lam : ℝ, Real.pi - threshold < lam ∧ AngleCap p lam := by
  classical
  let triples := (Finset.univ : Finset (V × V × V)).filter
    (fun t ↦ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)
  let angle (t : V × V × V) := EuclideanGeometry.angle (p t.1) (p t.2.1) (p t.2.2)
  let values := insert 0 (triples.image angle)
  have hnonempty : values.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hmax : values.max' hnonempty < threshold := by
    have hmem := Finset.max'_mem values hnonempty
    rcases Finset.mem_insert.mp hmem with hzero | hangle
    · simpa only [hzero] using hthreshold
    · obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hangle
      have hdistinct := (Finset.mem_filter.mp ht).2
      rw [← heq]
      exact hcap _ _ _ hdistinct.1 hdistinct.2.1 hdistinct.2.2
  refine ⟨Real.pi - (values.max' hnonempty + threshold) / 2, by linarith, ?_⟩
  intro a b c hab hac hbc
  have hmem : angle (a, b, c) ∈ values := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨(a, b, c), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hac, hbc⟩, rfl⟩
  have hle := Finset.le_max' values (angle (a, b, c)) hmem
  dsimp only [angle] at hle
  linarith

/-- Family A, including every finite cardinality and every planar degeneracy. -/
theorem planar_card_le_two_pow_of_strict_angles {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) (n : ℕ) (hn : 0 < n)
    (hcap : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      EuclideanGeometry.angle (p a) (p b) (p c) <
        Real.pi - Real.pi / ((n : ℝ) + 1 / 2)) : Fintype.card V ≤ 2 ^ n := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hperiod : 0 < (n : ℝ) + 1 / 2 := by positivity
  have hthreshold : 0 < Real.pi - Real.pi / ((n : ℝ) + 1 / 2) := by
    have hdiv : Real.pi / ((n : ℝ) + 1 / 2) < Real.pi :=
      (div_lt_iff₀ hperiod).mpr (by nlinarith [Real.pi_pos])
    linarith
  obtain ⟨lam, hstronger, hnewcap⟩ := exists_stronger_angleCap p hthreshold hcap
  have hlampos : 0 < lam := by
    have hdiv := div_pos Real.pi_pos hperiod
    linarith
  have hwidth : 0 < Real.pi / lam := div_pos Real.pi_pos hlampos
  have hbound : Real.pi / lam < (n : ℝ) + 1 / 2 := by
    apply (div_lt_iff₀ hlampos).mpr
    have h := (div_lt_iff₀ hperiod).mp
      (show Real.pi / ((n : ℝ) + 1 / 2) < lam by linarith)
    nlinarith
  exact planar_card_le_two_pow_of_width hp hnewcap hwidth
    (by rw [div_div_cancel₀ Real.pi_ne_zero]) n hn hbound

/-- Every configuration above the dyadic threshold forces the first claimed angle. -/
theorem planar_first_threshold_angle {V : Type*} [Fintype V]
    {p : V → Plane} (hp : Function.Injective p) (n : ℕ) (hn : 0 < n)
    (hcard : 2 ^ n < Fintype.card V) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Real.pi - Real.pi / ((n : ℝ) + 1 / 2) ≤
        EuclideanGeometry.angle (p a) (p b) (p c) := by
  by_contra! h
  have hcap := planar_card_le_two_pow_of_strict_angles hp n hn h
  omega

#print axioms planar_card_le_two_pow_of_width
#print axioms exists_stronger_angleCap
#print axioms planar_card_le_two_pow_of_strict_angles
#print axioms planar_first_threshold_angle

end JSP000404Research
