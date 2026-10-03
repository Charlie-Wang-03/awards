import JSP000404Research.FourSupportTwoAngleCore
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Sine-product obstruction for four-cycle angle patterns

The six 4-cycle derangements in the four-support-two angle terminal admit a
pure four-point obstruction.

For the standard cycle, the four selected angles are

* A: angle BAC in ABC,
* B: angle ABD in ABD,
* C: angle BCD in BCD,
* D: angle ADC in ACD.

The inverse cycle selects the other endpoint angle in each of these four
triangles.  The law of sines in the four triangles gives equality of the two
four-sine products: all side-length factors cancel.

Under the global angle cap, if a selected angle is at most delta*lam then the
paired inverse-cycle angle is at least lam minus that selected angle and at
most pi-lam.  For delta < 1/2 and lam <= pi/2 its sine is strictly larger.
Thus the two equal sine products would be strictly ordered, a contradiction.

This module is deliberately independent of the whole-cube / residual chain.
-/

namespace JSP000404Research

open Real

/-- A scalar sine comparison used by the four-cycle obstruction. -/
theorem sin_lt_sin_of_small_large_cap_core
    {x y delta lam : ℝ}
    (hx0 : 0 ≤ x)
    (hxSmall : x ≤ delta * lam)
    (hyLow : lam - x ≤ y)
    (hyCap : y ≤ Real.pi - lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2) :
    Real.sin x < Real.sin y := by
  have hxHalf : x < lam / 2 := by
    nlinarith
  have hxLam : x < lam := by
    nlinarith
  have hxPiHalf : x ≤ Real.pi / 2 := by
    linarith
  by_cases hyHalf : y ≤ Real.pi / 2
  · have hxy : x < y := by
      nlinarith
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hyHalf hxy
  · have hmirrorLow : lam ≤ Real.pi - y := by
      linarith
    have hxMirror : x < Real.pi - y := by
      linarith
    have hmirrorHalf : Real.pi - y ≤ Real.pi / 2 := by
      linarith
    have hsin :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hmirrorHalf hxMirror
    simpa using hsin

/-- In one triangle, a delta*lam-small angle has strictly smaller sine than
either other angle under the global cap. -/
theorem small_triangle_angle_sine_lt_other_core
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2)
    {i j k : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hsmall :
      EuclideanGeometry.angle (p j) (p i) (p k) ≤ delta * lam) :
    Real.sin (EuclideanGeometry.angle (p j) (p i) (p k)) <
      Real.sin (EuclideanGeometry.angle (p i) (p j) (p k)) := by
  let x := EuclideanGeometry.angle (p j) (p i) (p k)
  let y := EuclideanGeometry.angle (p i) (p j) (p k)
  let z := EuclideanGeometry.angle (p i) (p k) (p j)
  have hx0 : 0 ≤ x := by
    exact EuclideanGeometry.angle_nonneg _ _ _
  have hyCap : y ≤ Real.pi - lam :=
    hcap i j k hij hik hjk
  have hzCap : z ≤ Real.pi - lam :=
    hcap i k j hik hij hjk.symm
  have hsum : x + y + z = Real.pi := by
    simpa [x, y, z, EuclideanGeometry.angle_comm,
      add_assoc, add_left_comm, add_comm] using
      (EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := p j) (p₂ := p i) (p k) (hp.ne hij))
  have hyLow : lam - x ≤ y := by
    linarith
  exact sin_lt_sin_of_small_large_cap_core
    hx0 (by simpa [x] using hsmall) hyLow hyCap
    hdeltaHalf hlampos hlamHalf

/-- The standard four-cycle and its inverse have exactly the same product of
the four sines. -/
theorem four_cycle_sine_product_eq_core
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) *
      Real.sin (EuclideanGeometry.angle (p a) (p b) (p d)) *
      Real.sin (EuclideanGeometry.angle (p b) (p c) (p d)) *
      Real.sin (EuclideanGeometry.angle (p a) (p d) (p c))
    =
    Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
      Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
      Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) *
      Real.sin (EuclideanGeometry.angle (p a) (p c) (p d)) := by
  have hABC :
      Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) *
          dist (p a) (p c)
        =
      Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
          dist (p b) (p c) := by
    simpa [EuclideanGeometry.angle_comm, dist_comm] using
      (EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist
        (p b) (p a) (p c))
  have hABD :
      Real.sin (EuclideanGeometry.angle (p a) (p b) (p d)) *
          dist (p b) (p d)
        =
      Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
          dist (p a) (p d) := by
    simpa [EuclideanGeometry.angle_comm, dist_comm] using
      (EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist
        (p a) (p b) (p d))
  have hBCD :
      Real.sin (EuclideanGeometry.angle (p b) (p c) (p d)) *
          dist (p b) (p c)
        =
      Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) *
          dist (p b) (p d) := by
    simpa [EuclideanGeometry.angle_comm, dist_comm] using
      (EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist
        (p c) (p d) (p b)).symm
  have hACD :
      Real.sin (EuclideanGeometry.angle (p a) (p d) (p c)) *
          dist (p a) (p d)
        =
      Real.sin (EuclideanGeometry.angle (p a) (p c) (p d)) *
          dist (p a) (p c) := by
    simpa [EuclideanGeometry.angle_comm, dist_comm] using
      (EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist
        (p d) (p c) (p a)).symm
  let L :=
    dist (p a) (p c) * dist (p b) (p d) *
      dist (p b) (p c) * dist (p a) (p d)
  have hLne : L ≠ 0 := by
    dsimp [L]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (dist_ne_zero.mpr (hp.ne hac))
          (dist_ne_zero.mpr (hp.ne hbd)))
        (dist_ne_zero.mpr (hp.ne hbc)))
      (dist_ne_zero.mpr (hp.ne had))
  apply mul_right_cancel₀ hLne
  dsimp [L]
  calc
    (Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) *
        Real.sin (EuclideanGeometry.angle (p a) (p b) (p d)) *
        Real.sin (EuclideanGeometry.angle (p b) (p c) (p d)) *
        Real.sin (EuclideanGeometry.angle (p a) (p d) (p c))) *
        (dist (p a) (p c) * dist (p b) (p d) *
          dist (p b) (p c) * dist (p a) (p d))
      =
      (Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) *
          dist (p a) (p c)) *
      (Real.sin (EuclideanGeometry.angle (p a) (p b) (p d)) *
          dist (p b) (p d)) *
      (Real.sin (EuclideanGeometry.angle (p b) (p c) (p d)) *
          dist (p b) (p c)) *
      (Real.sin (EuclideanGeometry.angle (p a) (p d) (p c)) *
          dist (p a) (p d)) := by ring
    _ =
      (Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
          dist (p b) (p c)) *
      (Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
          dist (p a) (p d)) *
      (Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) *
          dist (p b) (p d)) *
      (Real.sin (EuclideanGeometry.angle (p a) (p c) (p d)) *
          dist (p a) (p c)) := by
        rw [hABC, hABD, hBCD, hACD]
    _ =
      (Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
        Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
        Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) *
        Real.sin (EuclideanGeometry.angle (p a) (p c) (p d))) *
        (dist (p a) (p c) * dist (p b) (p d) *
          dist (p b) (p c) * dist (p a) (p d)) := by ring

/-- A standard 4-cycle of delta*lam-small angles is impossible. -/
theorem four_cycle_small_angles_impossible_core
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hA :
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam)
    (hB :
      EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam)
    (hD :
      EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam) :
    False := by
  have hsA :=
    small_triangle_angle_sine_lt_other_core
      hp hcap hdeltaHalf hlampos hlamHalf
      hab hac hbc hA
  have hsB :=
    small_triangle_angle_sine_lt_other_core
      hp hcap hdeltaHalf hlampos hlamHalf
      hab.symm hbd had hB
  have hsC :
      Real.sin (EuclideanGeometry.angle (p b) (p c) (p d)) <
        Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) := by
    have h :=
      small_triangle_angle_sine_lt_other_core
        hp hcap hdeltaHalf hlampos hlamHalf
        hcd hbc.symm hbd.symm
        (by simpa [EuclideanGeometry.angle_comm] using hC)
    simpa [EuclideanGeometry.angle_comm] using h
  have hsD :
      Real.sin (EuclideanGeometry.angle (p a) (p d) (p c)) <
        Real.sin (EuclideanGeometry.angle (p a) (p c) (p d)) := by
    have h :=
      small_triangle_angle_sine_lt_other_core
        hp hcap hdeltaHalf hlampos hlamHalf
        hcd.symm had.symm hac.symm
        (by simpa [EuclideanGeometry.angle_comm] using hD)
    simpa [EuclideanGeometry.angle_comm] using h
  have hA0 :
      0 ≤ Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (EuclideanGeometry.angle_nonneg _ _ _)
      (EuclideanGeometry.angle_le_pi _ _ _)
  have hB0 :
      0 ≤ Real.sin (EuclideanGeometry.angle (p a) (p b) (p d)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (EuclideanGeometry.angle_nonneg _ _ _)
      (EuclideanGeometry.angle_le_pi _ _ _)
  have hC0 :
      0 ≤ Real.sin (EuclideanGeometry.angle (p b) (p c) (p d)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (EuclideanGeometry.angle_nonneg _ _ _)
      (EuclideanGeometry.angle_le_pi _ _ _)
  have hD0 :
      0 ≤ Real.sin (EuclideanGeometry.angle (p a) (p d) (p c)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (EuclideanGeometry.angle_nonneg _ _ _)
      (EuclideanGeometry.angle_le_pi _ _ _)
  have hA'0 :
      0 ≤ Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) :=
    (lt_of_le_of_lt hA0 hsA).le
  have hB'0 :
      0 ≤ Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) :=
    (lt_of_le_of_lt hB0 hsB).le
  have hC'0 :
      0 ≤ Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) :=
    (lt_of_le_of_lt hC0 hsC).le
  have hABCle :
      Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) *
          Real.sin (EuclideanGeometry.angle (p a) (p b) (p d)) *
          Real.sin (EuclideanGeometry.angle (p b) (p c) (p d))
        ≤
      Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
          Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
          Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) := by
    have hAB :
        Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) *
            Real.sin (EuclideanGeometry.angle (p a) (p b) (p d))
          ≤
        Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
            Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) :=
      mul_le_mul hsA.le hsB.le hB0 hA'0
    exact mul_le_mul hAB hsC.le hC0 (mul_nonneg hA'0 hB'0)
  have hrightABCpos :
      0 <
        Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
          Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
          Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) := by
    exact mul_pos
      (mul_pos
        (lt_of_le_of_lt hA0 hsA)
        (lt_of_le_of_lt hB0 hsB))
      (lt_of_le_of_lt hC0 hsC)
  have hprodLt :
      Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) *
        Real.sin (EuclideanGeometry.angle (p a) (p b) (p d)) *
        Real.sin (EuclideanGeometry.angle (p b) (p c) (p d)) *
        Real.sin (EuclideanGeometry.angle (p a) (p d) (p c))
      <
      Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
        Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
        Real.sin (EuclideanGeometry.angle (p b) (p d) (p c)) *
        Real.sin (EuclideanGeometry.angle (p a) (p c) (p d)) := by
    have hle :
        (Real.sin (EuclideanGeometry.angle (p b) (p a) (p c)) *
          Real.sin (EuclideanGeometry.angle (p a) (p b) (p d)) *
          Real.sin (EuclideanGeometry.angle (p b) (p c) (p d))) *
          Real.sin (EuclideanGeometry.angle (p a) (p d) (p c))
        ≤
        (Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
          Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
          Real.sin (EuclideanGeometry.angle (p b) (p d) (p c))) *
          Real.sin (EuclideanGeometry.angle (p a) (p d) (p c)) :=
      mul_le_mul_of_nonneg_right hABCle hD0
    have hlt :
        (Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
          Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
          Real.sin (EuclideanGeometry.angle (p b) (p d) (p c))) *
          Real.sin (EuclideanGeometry.angle (p a) (p d) (p c))
        <
        (Real.sin (EuclideanGeometry.angle (p a) (p b) (p c)) *
          Real.sin (EuclideanGeometry.angle (p b) (p a) (p d)) *
          Real.sin (EuclideanGeometry.angle (p b) (p d) (p c))) *
          Real.sin (EuclideanGeometry.angle (p a) (p c) (p d)) :=
      mul_lt_mul_of_pos_left hsD hrightABCpos
    exact hle.trans_lt hlt
  have hprodEq :=
    four_cycle_sine_product_eq_core hp
      hab hac had hbc hbd hcd
  rw [hprodEq] at hprodLt
  exact (lt_irrefl _ hprodLt)

/-- The three surviving derangements are exactly the three double
transpositions. -/
def FourSupportTwoAnglePattern3Core
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  (
    EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam ∧
    EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∧
    EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam ∧
    EuclideanGeometry.angle (p b) (p d) (p c) ≤ delta * lam
  )
  ∨
  (
    EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam ∧
    EuclideanGeometry.angle (p a) (p b) (p c) ≤ delta * lam ∧
    EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam ∧
    EuclideanGeometry.angle (p a) (p d) (p c) ≤ delta * lam
  )
  ∨
  (
    EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam ∧
    EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
    EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam ∧
    EuclideanGeometry.angle (p a) (p d) (p b) ≤ delta * lam
  )

/-- The nine angle derangements reduce to the three double transpositions.
The six discarded cases are all relabelings of the kernel-checked standard
four-cycle obstruction. -/
theorem four_supportTwo_angle_derangement_nine_reduce_to_three_core
    {V : Type*} {p : V → Plane}
    {delta lam : ℝ}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (hlampos : 0 < lam)
    (hlamHalf : lam ≤ Real.pi / 2)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h9 : FourSupportTwoAnglePattern9Core p delta lam a b c d) :
    FourSupportTwoAnglePattern3Core p delta lam a b c d := by
  unfold FourSupportTwoAnglePattern9Core at h9
  unfold FourChoiceDerangement9 at h9
  unfold FourSupportTwoAnglePattern3Core
  rcases h9 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact Or.inl h1
  · obtain ⟨hA,hB,hC,hD⟩ := h2
    exact False.elim
      (four_cycle_small_angles_impossible_core
        (p := p) hp hcap hdeltaHalf hlampos hlamHalf
        hab hac had hbc hbd hcd
        hA hB hC hD)
  · obtain ⟨hA,hB,hC,hD⟩ := h3
    exact False.elim
      (four_cycle_small_angles_impossible_core
        (p := p) hp hcap hdeltaHalf hlampos hlamHalf
        hac hab had hbc.symm hcd hbd
        (by simpa [EuclideanGeometry.angle_comm] using hA)
        hC hB hD)
  · obtain ⟨hA,hB,hC,hD⟩ := h4
    exact False.elim
      (four_cycle_small_angles_impossible_core
        (p := p) hp hcap hdeltaHalf hlampos hlamHalf
        hab had hac hbd hbc hcd.symm
        hA hB hD hC)
  · exact Or.inr (Or.inl h5)
  · obtain ⟨hA,hB,hC,hD⟩ := h6
    exact False.elim
      (four_cycle_small_angles_impossible_core
        (p := p) hp hcap hdeltaHalf hlampos hlamHalf
        had hab hac hbd.symm hcd.symm hbc
        (by simpa [EuclideanGeometry.angle_comm] using hA)
        hD
        (by simpa [EuclideanGeometry.angle_comm] using hB)
        hC)
  · obtain ⟨hA,hB,hC,hD⟩ := h7
    exact False.elim
      (four_cycle_small_angles_impossible_core
        (p := p) hp hcap hdeltaHalf hlampos hlamHalf
        had hac hab hcd.symm hbd.symm hbc.symm
        (by simpa [EuclideanGeometry.angle_comm] using hA)
        hD
        (by simpa [EuclideanGeometry.angle_comm] using hC)
        hB)
  · obtain ⟨hA,hB,hC,hD⟩ := h8
    exact False.elim
      (four_cycle_small_angles_impossible_core
        (p := p) hp hcap hdeltaHalf hlampos hlamHalf
        hac had hab hcd hbc hbd.symm
        hA hC
        (by simpa [EuclideanGeometry.angle_comm] using hD)
        hB)
  · exact Or.inr (Or.inr h9)

#print axioms sin_lt_sin_of_small_large_cap_core
#print axioms small_triangle_angle_sine_lt_other_core
#print axioms four_cycle_sine_product_eq_core
#print axioms four_cycle_small_angles_impossible_core
#print axioms four_supportTwo_angle_derangement_nine_reduce_to_three_core

end JSP000404Research
