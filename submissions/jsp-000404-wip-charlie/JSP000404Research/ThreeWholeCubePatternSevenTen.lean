import JSP000404Research.SupportOneNarrowCone
import JSP000404Research.QTTTThreeSupportSmallPairMatching
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-!
# Eliminate two eleven-state patterns beside a support-one fourth centre

In the saturated three-whole-cube terminal with a unique support-one fourth
vertex d, the support-one narrow-cone theorem bounds every angle at d by
(1+delta)*lambda.

Two of the eleven crossed three-support-two patterns then become impossible
without any hull-cycle analysis.
-/

namespace JSP000404Research

theorem three_one_add_three_delta_lam_lt_two_pi
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t) :
    3 * (1 + 3 * delta) * lam < 2 * Real.pi := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hcoeff :
      3 * (1 + 3 * delta) < 2 * t := by
    rw [ht]
    push_cast
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hmul :=
    mul_lt_mul_of_pos_right hcoeff hlampos
  have hpi : t * lam = Real.pi := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  rw [mul_assoc, hpi] at hmul
  simpa [mul_add, add_mul] using hmul

theorem cyclic_three_delta_angles_beside_narrow_fourth_impossible
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hA :
      EuclideanGeometry.angle (p b) (p a) (p d)
        ≤ delta * lam)
    (hB :
      EuclideanGeometry.angle (p c) (p b) (p d)
        ≤ delta * lam)
    (hC :
      EuclideanGeometry.angle (p a) (p c) (p d)
        ≤ delta * lam)
    (hdAB :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam)
    (hdAC :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam)
    (hdBC :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam) :
    False := by
  have htriACD :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p c) (p₂ := p a) (p d)
      (hp.ne hac.symm)
  have htriABD :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p a) (p₂ := p b) (p d)
      (hp.ne hab)
  have htriBCD :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p c) (p d)
      (hp.ne hbc)

  have hlargeA :
      Real.pi - (1 + 2 * delta) * lam
        ≤ EuclideanGeometry.angle (p c) (p a) (p d) := by
    have hdAC' :
        EuclideanGeometry.angle (p c) (p d) (p a)
          ≤ (1 + delta) * lam := by
      simpa [EuclideanGeometry.angle_comm] using hdAC
    nlinarith
  have hlargeB :
      Real.pi - (1 + 2 * delta) * lam
        ≤ EuclideanGeometry.angle (p a) (p b) (p d) := by
    nlinarith
  have hlargeC :
      Real.pi - (1 + 2 * delta) * lam
        ≤ EuclideanGeometry.angle (p b) (p c) (p d) := by
    nlinarith

  have hsubA :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p a) (p c) (p b) (p d)
  have hsubB :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p b) (p a) (p c) (p d)
  have hsubC :=
    EuclideanGeometry.angle_le_angle_add_angle
      (p c) (p b) (p a) (p d)

  have hABC_A :
      Real.pi - (1 + 3 * delta) * lam
        ≤ EuclideanGeometry.angle (p b) (p a) (p c) := by
    have hsubA' :
        EuclideanGeometry.angle (p c) (p a) (p d)
          ≤
        EuclideanGeometry.angle (p b) (p a) (p c) +
          EuclideanGeometry.angle (p b) (p a) (p d) := by
      simpa [EuclideanGeometry.angle_comm, add_comm] using hsubA
    nlinarith
  have hABC_B :
      Real.pi - (1 + 3 * delta) * lam
        ≤ EuclideanGeometry.angle (p a) (p b) (p c) := by
    have hsubB' :
        EuclideanGeometry.angle (p a) (p b) (p d)
          ≤
        EuclideanGeometry.angle (p a) (p b) (p c) +
          EuclideanGeometry.angle (p c) (p b) (p d) := by
      simpa using hsubB
    nlinarith
  have hABC_C :
      Real.pi - (1 + 3 * delta) * lam
        ≤ EuclideanGeometry.angle (p a) (p c) (p b) := by
    have hsubC' :
        EuclideanGeometry.angle (p b) (p c) (p d)
          ≤
        EuclideanGeometry.angle (p a) (p c) (p b) +
          EuclideanGeometry.angle (p a) (p c) (p d) := by
      simpa [EuclideanGeometry.angle_comm, add_comm] using hsubC
    nlinarith

  have hABC :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p a) (p₂ := p b) (p c)
      (hp.ne hab)
  have hbound :=
    three_one_add_three_delta_lam_lt_two_pi
      hn4 hdelta0 hdeltaHalf ht hlam
  nlinarith

theorem threeSupport_pattern7_impossible_beside_supportOne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hpat :
      EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam)
    (hdAB :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam)
    (hdAC :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam)
    (hdBC :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam) :
    False :=
  cyclic_three_delta_angles_beside_narrow_fourth_impossible
    hp hn4 hdelta0 hdeltaHalf ht hlam
    hab hac had hbc hbd hcd
    hpat.1 hpat.2.1 hpat.2.2
    hdAB hdAC hdBC

theorem threeSupport_pattern10_impossible_beside_supportOne
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hpat :
      EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam)
    (hdAB :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam)
    (hdAC :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam)
    (hdBC :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam) :
    False := by
  exact cyclic_three_delta_angles_beside_narrow_fourth_impossible
    hp hn4 hdelta0 hdeltaHalf ht hlam
    hac hab had hbc.symm hcd hbd
    hpat.1
    (by simpa [EuclideanGeometry.angle_comm] using hpat.2.2)
    hpat.2.1
    (by simpa [EuclideanGeometry.angle_comm] using hdAC)
    hdAB
    (by simpa [EuclideanGeometry.angle_comm] using hdBC)

#print axioms threeSupport_pattern7_impossible_beside_supportOne
#print axioms threeSupport_pattern10_impossible_beside_supportOne

end JSP000404Research
