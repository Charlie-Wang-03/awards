import JSP000404Research.ThreeWholeCubeSourceMinTwoState
import Mathlib.Tactic

/-!
# Source-max three-whole-cube terminal reduces to two crossed states

When the whole-cube source d is the global maximum and the partners satisfy
a<b<c<d, the internal edge matrix gives all three star angles at a below
lambda and also angle(c,b,d)<lambda.

Together with the support-one narrow cone at d, the same triangle-sum
contradiction used in the source-min branch eliminates states 1--5 and 7--10.
Only original states 6 and 11 remain.
-/

namespace JSP000404Research

def SourceMaxThreeSupportTwoState2
    {V : Type*}
    (p : V → Plane) (delta lam : ℝ)
    (a b c d : V) : Prop :=
  let A_bd := EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam
  let A_cd := EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam
  let B_cd := EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam
  let C_ab := EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam
  (A_bd ∧ B_cd ∧ C_ab) ∨
  (A_cd ∧ B_cd ∧ C_ab)

theorem eleven_reduce_to_two_of_sourceMax_angle_rigidity
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
    (hA_bd_lt :
      EuclideanGeometry.angle (p b) (p a) (p d) < lam)
    (hA_cd_lt :
      EuclideanGeometry.angle (p c) (p a) (p d) < lam)
    (hA_bc_lt :
      EuclideanGeometry.angle (p b) (p a) (p c) < lam)
    (hB_cd_lt :
      EuclideanGeometry.angle (p c) (p b) (p d) < lam)
    (hD_ab :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam)
    (hD_ac :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam)
    (hD_bc :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam) :
    SourceMaxThreeSupportTwoState2 p delta lam a b c d := by
  unfold ThreeSupportTwoCrossedPattern11 at h11
  unfold SourceMaxThreeSupportTwoState2
  rcases h11 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11'
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hac had h1.2.1 hA_cd_lt hD_ac
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hab had h2.2.1 hA_bd_lt hD_ab
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hac had h3.2.2 hA_cd_lt hD_ac
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hac had h4.2.2 hA_cd_lt hD_ac
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hbc hbd h5.2.2 hB_cd_lt
      (by simpa [EuclideanGeometry.angle_comm] using hD_bc)
  · exact Or.inl h6
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hac had h7.2.2 hA_cd_lt hD_ac
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hbc hbd h8.2.2 hB_cd_lt
      (by simpa [EuclideanGeometry.angle_comm] using hD_bc)
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hab had h9.2.1 hA_bd_lt hD_ab
  · exfalso
    exact impossible_delta_one_one_add_delta_triangle
      hp hn4 hdelta0 hdeltaHalf ht hlam
      hab had h10.2.1 hA_bd_lt hD_ab
  · exact Or.inr h11'

#print axioms eleven_reduce_to_two_of_sourceMax_angle_rigidity

end JSP000404Research
