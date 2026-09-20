import JSP000404Research.TriangleSignParity
import JSP000404Research.SignedRayAngle
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Quantitative transfer of a same-sign triangle gap

For three distinct vertices i,j,k, suppose the two triangle rays at i have the
same canonical sign while the two triangle rays at j have opposite canonical
signs.

At i, the genuine triangle angle is exactly the canonical projective
separation.

At j, the genuine triangle angle is the supplement of the canonical
projective separation.  Since the three Euclidean triangle angles sum to pi,

  projectiveSep(j) = pi - angle_j
                   = angle_i + angle_k
                   >= angle_i
                   = projectiveSep(i).

Thus every normalized quotient credit carried by the same-sign gap at i may be
transferred, without loss, to the opposite-sign projective interval at j.

This is the quantitative second-payment mechanism for separated support-two
centres suggested by triangle sign parity.
-/

namespace JSP000404Research

open Real

/-- Same-sign triangle gap at i transfers without loss to an opposite-sign
projective separation at j. -/
theorem triangle_projective_separation_transfer
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j k : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi :
      raySignAt hp i ⟨j, hij.symm⟩ =
        raySignAt hp i ⟨k, hik.symm⟩)
    (hj :
      raySignAt hp j ⟨i, hij⟩ ≠
        raySignAt hp j ⟨k, hjk.symm⟩) :
    |rayThetaAt hp i ⟨j, hij.symm⟩ -
        rayThetaAt hp i ⟨k, hik.symm⟩|
      ≤
    |rayThetaAt hp j ⟨i, hij⟩ -
        rayThetaAt hp j ⟨k, hjk.symm⟩| := by
  let ij_i : OtherVertex i := ⟨j, hij.symm⟩
  let ik_i : OtherVertex i := ⟨k, hik.symm⟩
  let ji_j : OtherVertex j := ⟨i, hij⟩
  let jk_j : OtherVertex j := ⟨k, hjk.symm⟩

  have hdiffIlt :
      |rayThetaAt hp i ij_i - rayThetaAt hp i ik_i| < Real.pi := by
    rw [abs_lt]
    constructor
    · have h1 := rayThetaAt_nonneg hp i ij_i
      have h2 := rayThetaAt_lt_pi hp i ik_i
      linarith
    · have h1 := rayThetaAt_nonneg hp i ik_i
      have h2 := rayThetaAt_lt_pi hp i ij_i
      linarith
  have hdiffJlt :
      |rayThetaAt hp j ji_j - rayThetaAt hp j jk_j| < Real.pi := by
    rw [abs_lt]
    constructor
    · have h1 := rayThetaAt_nonneg hp j ji_j
      have h2 := rayThetaAt_lt_pi hp j jk_j
      linarith
    · have h1 := rayThetaAt_nonneg hp j jk_j
      have h2 := rayThetaAt_lt_pi hp j ji_j
      linarith

  have hi' :
      raySignAt hp i ij_i = raySignAt hp i ik_i := by
    simpa [ij_i, ik_i] using hi
  have hj' :
      raySignAt hp j ji_j ≠ raySignAt hp j jk_j := by
    simpa [ji_j, jk_j] using hj

  have hangleI :
      EuclideanGeometry.angle (p j) (p i) (p k) =
        |rayThetaAt hp i ij_i - rayThetaAt hp i ik_i| := by
    change
      InnerProductGeometry.angle
          (p j - p i) (p k - p i)
        =
      |rayThetaAt hp i ij_i - rayThetaAt hp i ik_i|
    rw [rayRepAt_eq hp i ij_i, rayRepAt_eq hp i ik_i,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp i ij_i)
        (rayRhoAt_pos hp i ik_i)]
    exact angle_signedRayDirection_eq_of_sign_eq
      hi' hdiffIlt.le

  have hangleJ :
      EuclideanGeometry.angle (p i) (p j) (p k) =
        Real.pi -
          |rayThetaAt hp j ji_j - rayThetaAt hp j jk_j| := by
    change
      InnerProductGeometry.angle
          (p i - p j) (p k - p j)
        =
      Real.pi -
        |rayThetaAt hp j ji_j - rayThetaAt hp j jk_j|
    rw [rayRepAt_eq hp j ji_j, rayRepAt_eq hp j jk_j,
      angle_positive_smul_signedRay
        (rayRhoAt_pos hp j ji_j)
        (rayRhoAt_pos hp j jk_j)]
    exact angle_signedRayDirection_eq_pi_sub_of_sign_ne
      hj' hdiffJlt.le

  have hpji : p j ≠ p i := by
    intro h
    apply hij
    exact hp h.symm

  have hsum :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := p i) (p₂ := p j) (p k) hpji
  have hcomm :
      EuclideanGeometry.angle (p k) (p i) (p j) =
        EuclideanGeometry.angle (p j) (p i) (p k) :=
    EuclideanGeometry.angle_comm _ _ _
  rw [hangleJ, hcomm, hangleI] at hsum
  have hangleK0 :
      0 ≤ EuclideanGeometry.angle (p j) (p k) (p i) :=
    EuclideanGeometry.angle_nonneg _ _ _
  linarith

/-- By triangle sign parity, a same-sign gap at i always transfers to one of
the other two vertices. -/
theorem triangle_same_sign_gap_transfers_to_one_neighbor
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j k : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi :
      raySignAt hp i ⟨j, hij.symm⟩ =
        raySignAt hp i ⟨k, hik.symm⟩) :
    (
      raySignAt hp j ⟨i, hij⟩ ≠
        raySignAt hp j ⟨k, hjk.symm⟩ ∧
      |rayThetaAt hp i ⟨j, hij.symm⟩ -
          rayThetaAt hp i ⟨k, hik.symm⟩|
        ≤
      |rayThetaAt hp j ⟨i, hij⟩ -
          rayThetaAt hp j ⟨k, hjk.symm⟩|
    ) ∨
    (
      raySignAt hp k ⟨i, hik⟩ ≠
        raySignAt hp k ⟨j, hjk⟩ ∧
      |rayThetaAt hp i ⟨j, hij.symm⟩ -
          rayThetaAt hp i ⟨k, hik.symm⟩|
        ≤
      |rayThetaAt hp k ⟨i, hik⟩ -
          rayThetaAt hp k ⟨j, hjk⟩|
    ) := by
  rcases triangle_exactly_one_other_sign_transition
      hp hij hik hjk hi with hj | hk
  · left
    refine ⟨hj.1, ?_⟩
    exact triangle_projective_separation_transfer
      hp hij hik hjk hi hj.1
  · right
    refine ⟨hk.2, ?_⟩
    -- Same transfer after swapping j and k.
    have hki_same :
        raySignAt hp i ⟨k, hik.symm⟩ =
          raySignAt hp i ⟨j, hij.symm⟩ := hi.symm
    have htransfer :=
      triangle_projective_separation_transfer
        hp hik hij hjk.symm hki_same hk.2
    simpa [abs_sub_comm] using htransfer

/-- Any normalized quotient lower bound on the hidden same-sign gap transfers
to the opposite-sign neighbour interval. -/
theorem triangle_quotient_credit_transfer
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j k : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi :
      raySignAt hp i ⟨j, hij.symm⟩ =
        raySignAt hp i ⟨k, hik.symm⟩)
    {q : ℕ} {t : ℝ}
    (ht : 0 ≤ t)
    (hq :
      (q : ℝ) ≤
        t * (
          |rayThetaAt hp i ⟨j, hij.symm⟩ -
            rayThetaAt hp i ⟨k, hik.symm⟩| / Real.pi)) :
    (
      raySignAt hp j ⟨i, hij⟩ ≠
        raySignAt hp j ⟨k, hjk.symm⟩ ∧
      (q : ℝ) ≤
        t * (
          |rayThetaAt hp j ⟨i, hij⟩ -
            rayThetaAt hp j ⟨k, hjk.symm⟩| / Real.pi)
    ) ∨
    (
      raySignAt hp k ⟨i, hik⟩ ≠
        raySignAt hp k ⟨j, hjk⟩ ∧
      (q : ℝ) ≤
        t * (
          |rayThetaAt hp k ⟨i, hik⟩ -
            rayThetaAt hp k ⟨j, hjk⟩| / Real.pi)
    ) := by
  rcases triangle_same_sign_gap_transfers_to_one_neighbor
      hp hij hik hjk hi with hj | hk
  · left
    refine ⟨hj.1, ?_⟩
    have hdiv :
        |rayThetaAt hp i ⟨j, hij.symm⟩ -
            rayThetaAt hp i ⟨k, hik.symm⟩| / Real.pi
          ≤
        |rayThetaAt hp j ⟨i, hij⟩ -
            rayThetaAt hp j ⟨k, hjk.symm⟩| / Real.pi := by
      exact div_le_div_of_nonneg_right hj.2 Real.pi_pos.le
    exact hq.trans
      (mul_le_mul_of_nonneg_left hdiv ht)
  · right
    refine ⟨hk.1, ?_⟩
    have hdiv :
        |rayThetaAt hp i ⟨j, hij.symm⟩ -
            rayThetaAt hp i ⟨k, hik.symm⟩| / Real.pi
          ≤
        |rayThetaAt hp k ⟨i, hik⟩ -
            rayThetaAt hp k ⟨j, hjk⟩| / Real.pi := by
      exact div_le_div_of_nonneg_right hk.2 Real.pi_pos.le
    exact hq.trans
      (mul_le_mul_of_nonneg_left hdiv ht)

#print axioms triangle_projective_separation_transfer
#print axioms triangle_same_sign_gap_transfers_to_one_neighbor
#print axioms triangle_quotient_credit_transfer

end JSP000404Research
