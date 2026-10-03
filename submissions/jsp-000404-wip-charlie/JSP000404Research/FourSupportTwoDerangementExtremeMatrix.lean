import JSP000404Research.FourSupportTwoDerangement
import JSP000404Research.ThreeWholeCubeSourceExtremePatternReduction
import Mathlib.Tactic

/-!
# Nine derangement patterns are incompatible with a source-extreme angle matrix

The whole-cube retained-code star supplies a rigid same-band angle matrix when
its source is the global minimum or global maximum.  In either orientation,
every K4 derangement small-pair pattern contains a delta-small angle at a
different vertex of a triangle from one of these strict sub-lambda angles.

The third angle is bounded by lambda by AngleCap.  Hence the triangle angle
sum would be strictly below pi.  Therefore the all-four-support-two
derangement terminal cannot coexist with a source-extreme whole-cube angle
matrix.
-/

namespace JSP000404Research

theorem delta_small_and_distinct_unit_angle_impossible
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hbc : b ≠ c)
    (hsmall :
      EuclideanGeometry.angle (p b) (p a) (p c)
        ≤ delta * lam)
    (hunit :
      EuclideanGeometry.angle (p a) (p b) (p c)
        < lam) :
    False := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hthird0 :
      EuclideanGeometry.angle (p a) (p c) (p b) ≤ lam := by
    exact hcap c a b hac.symm hbc.symm hab
  have hthird :
      EuclideanGeometry.angle (p a) (p c) (p b)
        ≤ (1 + delta) * lam := by
    nlinarith
  exact delta_one_oneAddDelta_triangle_impossible
    hp hn4 hdelta0 hdeltaHalf ht hlam
    hab hsmall hunit hthird

/-- Global-min source matrix:
  C_ab < lambda, D_ab < lambda, D_ac < lambda, D_bc < lambda.
No nine-state derangement can survive. -/
theorem fourSupportTwo_derangement_impossible_of_sourceMin_matrix
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
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
      FourSupportTwoDerangementPattern9 p delta lam a b c d)
    (hCab :
      EuclideanGeometry.angle (p a) (p c) (p b) < lam)
    (hDab :
      EuclideanGeometry.angle (p a) (p d) (p b) < lam)
    (hDac :
      EuclideanGeometry.angle (p a) (p d) (p c) < lam)
    (_hDbc :
      EuclideanGeometry.angle (p b) (p d) (p c) < lam) :
    False := by
  have killABC_A_C
      (h :
        EuclideanGeometry.angle (p b) (p a) (p c)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hac hab hbc.symm
      (by simpa [EuclideanGeometry.angle_comm] using h)
      hCab

  have killABC_B_C
      (h :
        EuclideanGeometry.angle (p a) (p b) (p c)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hbc hab.symm hac.symm
      (by simpa [EuclideanGeometry.angle_comm] using h)
      (by simpa [EuclideanGeometry.angle_comm] using hCab)

  have killABD_A_D
      (h :
        EuclideanGeometry.angle (p b) (p a) (p d)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      had hab hbd.symm
      (by simpa [EuclideanGeometry.angle_comm] using h)
      hDab

  have killABD_B_D
      (h :
        EuclideanGeometry.angle (p a) (p b) (p d)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hbd hab.symm had.symm
      (by simpa [EuclideanGeometry.angle_comm] using h)
      (by simpa [EuclideanGeometry.angle_comm] using hDab)

  have killACD_A_D
      (h :
        EuclideanGeometry.angle (p c) (p a) (p d)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      had hac hcd.symm
      (by simpa [EuclideanGeometry.angle_comm] using h)
      hDac

  unfold FourSupportTwoDerangementPattern9 at hpat
  rcases hpat with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact killABC_A_C h1.1
  · exact killABC_A_C h2.1
  · exact killABC_A_C h3.1
  · exact killABC_B_C h4.2.1
  · exact killABC_B_C h5.2.1
  · exact killABD_A_D h6.1
  · exact killABC_B_C h7.2.1
  · exact killABD_B_D h8.2.1
  · exact killACD_A_D h9.1

/-- Global-max source matrix:
  B_ac < lambda, B_ad < lambda, B_cd < lambda, C_ad < lambda.
Again no nine-state derangement can survive. -/
theorem fourSupportTwo_derangement_impossible_of_sourceMax_matrix
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
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
      FourSupportTwoDerangementPattern9 p delta lam a b c d)
    (hBac :
      EuclideanGeometry.angle (p a) (p b) (p c) < lam)
    (hBad :
      EuclideanGeometry.angle (p a) (p b) (p d) < lam)
    (_hBcd :
      EuclideanGeometry.angle (p c) (p b) (p d) < lam)
    (_hCad :
      EuclideanGeometry.angle (p a) (p c) (p d) < lam) :
    False := by
  have killABC_A_B
      (h :
        EuclideanGeometry.angle (p b) (p a) (p c)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hab hac hbc
      h hBac

  have killABD_A_B
      (h :
        EuclideanGeometry.angle (p b) (p a) (p d)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hab had hbd
      h hBad

  have killABC_C_B
      (h :
        EuclideanGeometry.angle (p a) (p c) (p b)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hbc hac.symm hab.symm
      (by simpa [EuclideanGeometry.angle_comm] using h)
      (by simpa [EuclideanGeometry.angle_comm] using hBac)

  have killABD_D_B
      (h :
        EuclideanGeometry.angle (p a) (p d) (p b)
          ≤ delta * lam) : False := by
    exact delta_small_and_distinct_unit_angle_impossible
      hp hcap hn4 hdelta0 hdeltaHalf ht hlam
      hbd had.symm hab.symm
      (by simpa [EuclideanGeometry.angle_comm] using h)
      (by simpa [EuclideanGeometry.angle_comm] using hBad)

  unfold FourSupportTwoDerangementPattern9 at hpat
  rcases hpat with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact killABC_A_B h1.1
  · exact killABC_A_B h2.1
  · exact killABC_A_B h3.1
  · exact killABD_A_B h4.1
  · exact killABD_A_B h5.1
  · exact killABC_C_B h6.2.2.1
  · exact killABD_D_B h7.2.2.2
  · exact killABC_C_B h8.2.2.1
  · exact killABC_C_B h9.2.2.1

#print axioms delta_small_and_distinct_unit_angle_impossible
#print axioms fourSupportTwo_derangement_impossible_of_sourceMin_matrix
#print axioms fourSupportTwo_derangement_impossible_of_sourceMax_matrix

end JSP000404Research
