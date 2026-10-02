import JSP000404Research.ProjectionThreeWholeCubeSourceExtremeAngles
import JSP000404Research.QTTTThreeSupportSmallPairMatching
import Mathlib.Tactic

/-!
# Source-min three-whole-cube terminal reduces to two crossed states

When the whole-cube source d is the global minimum and the three partners are
ordered a<b<c, the internal edge-colour matrix plus same-band geometry gives

  angle(d,b,a) < lambda,
  angle(d,c,a) < lambda,
  angle(d,c,b) < lambda.

The support-one source d also satisfies the global narrow-cone bound
  every angle at d <= (1+delta)*lambda.

Therefore any triangle containing
* one delta-small angle,
* one same-band angle < lambda,
* one source angle <= (1+delta)*lambda
has total angle strictly below pi, because
  delta + 1 + (1+delta) = 2+2delta < n+delta = t
for n>=4 and delta<1/2.

This kills states 3--11 of the eleven-state terminal; only states 1 and 2
remain.
-/

namespace JSP000404Research

theorem impossible_delta_one_one_add_delta_triangle
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hn4 : 4 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {a b c : V}
    (hab : a ≠ b)
    (hac : a ≠ c)
    (hA :
      EuclideanGeometry.angle (p b) (p a) (p c)
        ≤ delta * lam)
    (hB :
      EuclideanGeometry.angle (p a) (p b) (p c)
        < lam)
    (hC :
      EuclideanGeometry.angle (p a) (p c) (p b)
        ≤ (1 + delta) * lam) :
    False := by
  have htpos :
      0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos Real.pi_pos htpos
  have hcoeff :
      delta + 1 + (1 + delta) < t := by
    rw [ht]
    push_cast
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hmul :=
    mul_lt_mul_of_pos_right hcoeff hlampos
  have hpi : t * lam = Real.pi := by
    rw [hlam]
    field_simp [ne_of_gt htpos]
  have hsumBound :
      delta * lam + lam + (1 + delta) * lam < Real.pi := by
    rw [← hpi]
    nlinarith
  have htri :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p a) (p₂ := p b) (p c)
      (hp.ne hab)
  nlinarith

def SourceMinThreeSupportTwoState2
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  let A_bc := EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam
  let B_ad := EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam
  let C_ad := EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam
  let C_bd := EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam
  (A_bc ∧ B_ad ∧ C_ad) ∨
  (A_bc ∧ B_ad ∧ C_bd)

theorem eleven_reduce_to_two_of_sourceMin_angle_rigidity
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
    (h11 : ThreeSupportTwoCrossedPattern11 p delta lam a b c d)
    (hB_ad_lt :
      EuclideanGeometry.angle (p a) (p b) (p d) < lam)
    (hC_ad_lt :
      EuclideanGeometry.angle (p a) (p c) (p d) < lam)
    (hC_bd_lt :
      EuclideanGeometry.angle (p b) (p c) (p d) < lam)
    (hD_ab :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam)
    (hD_ac :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam)
    (hD_bc :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam) :
    SourceMinThreeSupportTwoState2 p delta lam a b c d := by
  unfold ThreeSupportTwoCrossedPattern11 at h11
  unfold SourceMinThreeSupportTwoState2
  rcases h11 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11'
  · exact Or.inl h1
  · exact Or.inr h2
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hbc hbd h3.2.1 hC_bd_lt
      (by simpa [EuclideanGeometry.angle_comm] using hD_bc)
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hab had h4.1 hB_ad_lt hD_ab
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hab had h5.1 hB_ad_lt hD_ab
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hab had h6.1 hB_ad_lt hD_ab
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hab had h7.1 hB_ad_lt hD_ab
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hac had h8.1 hC_ad_lt hD_ac
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hac had h9.1 hC_ad_lt hD_ac
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hac had h10.1 hC_ad_lt hD_ac
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hac had h11'.1 hC_ad_lt hD_ac

#print axioms impossible_delta_one_one_add_delta_triangle
#print axioms eleven_reduce_to_two_of_sourceMin_angle_rigidity

end JSP000404Research
