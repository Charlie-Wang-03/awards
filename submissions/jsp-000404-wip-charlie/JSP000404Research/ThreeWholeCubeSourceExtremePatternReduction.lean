import JSP000404Research.ProjectionThreeWholeCubeSourceExtremeAngles
import JSP000404Research.SupportOneNarrowCone
import JSP000404Research.QTTTThreeSupportSmallPairMatching
import Mathlib.Tactic

/-!
# Four-state reduction for a source-extreme saturated whole-cube star

When the unique support-one vertex is the source v, it is a global order
extreme.  The whole-cube internal edge matrix then gives several same-band
angles strictly below lambda among the three support-two partners.

Combining one such <lambda angle with:
* one delta*lambda small-pair angle from the eleven-state terminal, and
* one (1+delta)*lambda support-one cone angle at v,

forces a triangle angle sum below pi.  This eliminates nine of the eleven
states.

For a global-min source only states 1 and 2 survive.
For a global-max source only states 6 and 11 survive.
-/

namespace JSP000404Research

theorem delta_one_oneAddDelta_triangle_impossible
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
    (hsmall :
      EuclideanGeometry.angle (p b) (p a) (p c)
        ≤ delta * lam)
    (hunit :
      EuclideanGeometry.angle (p a) (p b) (p c)
        < lam)
    (hcone :
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
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hmul :
      (delta + 1 + (1 + delta)) * lam < Real.pi := by
    have h := mul_lt_mul_of_pos_right hcoeff hlampos
    have hpi : t * lam = Real.pi := by
      rw [hlam]
      field_simp [ne_of_gt htpos]
    rw [hpi] at h
    exact h
  have htri :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p b) (p₂ := p a) (p c)
      (hp.ne hab.symm)
  have htri' :
      EuclideanGeometry.angle (p b) (p a) (p c) +
      EuclideanGeometry.angle (p a) (p b) (p c) +
      EuclideanGeometry.angle (p a) (p c) (p b)
        = Real.pi := by
    simpa [EuclideanGeometry.angle_comm] using htri
  nlinarith

/-- Under the global-min source angle matrix, an eleven-state pattern reduces
to state 1 or state 2. -/
theorem threeSupport_eleven_reduce_to_one_or_two_of_sourceMin_angles
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
    (hpat : ThreeSupportTwoCrossedPattern11 p delta lam a b c d)
    (hBad :
      EuclideanGeometry.angle (p a) (p b) (p d) < lam)
    (hCab :
      EuclideanGeometry.angle (p a) (p c) (p b) < lam)
    (hCad :
      EuclideanGeometry.angle (p a) (p c) (p d) < lam)
    (hCbd :
      EuclideanGeometry.angle (p b) (p c) (p d) < lam)
    (hdAB :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam)
    (hdAC :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam)
    (hdBC :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam) :
    (
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p c) (p d) ≤ delta * lam
    )
    ∨
    (
      EuclideanGeometry.angle (p b) (p a) (p c) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p b) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p b) (p c) (p d) ≤ delta * lam
    ) := by
  unfold ThreeSupportTwoCrossedPattern11 at hpat
  rcases hpat with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact Or.inl h1
  · exact Or.inr h2
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hbc
        h3.2.1 hCbd hdBC)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        had
        h4.1 hBad hdAB)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        had
        h5.1 hBad hdAB)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        had
        h6.1 hBad hdAB)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        had
        h7.1 hBad hdAB)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hac
        h8.1 hCad hdAC)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hac
        h9.1 hCad hdAC)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hac
        h10.1 hCad hdAC)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hac
        h11.1 hCad hdAC)

/-- Under the global-max source angle matrix, an eleven-state pattern reduces
to state 6 or state 11. -/
theorem threeSupport_eleven_reduce_to_six_or_eleven_of_sourceMax_angles
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
    (hpat : ThreeSupportTwoCrossedPattern11 p delta lam a b c d)
    (hAbc :
      EuclideanGeometry.angle (p b) (p a) (p c) < lam)
    (hAbd :
      EuclideanGeometry.angle (p b) (p a) (p d) < lam)
    (hAcd :
      EuclideanGeometry.angle (p c) (p a) (p d) < lam)
    (hBcd :
      EuclideanGeometry.angle (p c) (p b) (p d) < lam)
    (hdAB :
      EuclideanGeometry.angle (p a) (p d) (p b)
        ≤ (1 + delta) * lam)
    (hdAC :
      EuclideanGeometry.angle (p a) (p d) (p c)
        ≤ (1 + delta) * lam)
    (hdBC :
      EuclideanGeometry.angle (p b) (p d) (p c)
        ≤ (1 + delta) * lam) :
    (
      EuclideanGeometry.angle (p b) (p a) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam
    )
    ∨
    (
      EuclideanGeometry.angle (p c) (p a) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p c) (p b) (p d) ≤ delta * lam ∧
      EuclideanGeometry.angle (p a) (p c) (p b) ≤ delta * lam
    ) := by
  unfold ThreeSupportTwoCrossedPattern11 at hpat
  rcases hpat with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        had h1.2.1 hAbd hdAB)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        had h2.2.1 hAbd hdAB)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hac h3.2.2 hAcd hdAC)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hac h4.2.2 hAcd hdAC)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hbc h5.2.2 hBcd hdBC)
  · exact Or.inl h6
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hac h7.2.2 hAcd hdAC)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        hbc h8.2.2 hBcd hdBC)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        had h9.2.1 hAbd hdAB)
  · exact False.elim
      (delta_one_oneAddDelta_triangle_impossible
        hp hn4 hdelta0 hdeltaHalf ht hlam
        had h10.2.1 hAbd hdAB)
  · exact Or.inr h11

#print axioms delta_one_oneAddDelta_triangle_impossible
#print axioms threeSupport_eleven_reduce_to_one_or_two_of_sourceMin_angles
#print axioms threeSupport_eleven_reduce_to_six_or_eleven_of_sourceMax_angles

end JSP000404Research
