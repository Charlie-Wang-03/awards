import JSP000404Research.StrictSupportCone
import JSP000404Research.AngleCirclePacking
import JSP000404Research.SignedRayMonodromy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic

/-!
# Strict-support arcs on the angle circle

Real.Angle is exactly AddCircle (2*pi). We use this to place the open
dual-support interval from StrictSupportCone directly on the direction circle.

For a same-sign ray interval [a,a+w], w<pi, the strict supporting parameters
form

  (a+w-pi/2, a+pi/2),

of length pi-w.

For sign=true this interval is used directly. For sign=false the corresponding
ordinary unit-vector angles are shifted by pi.

Thus each centre receives a genuine metric ball on Real.Angle, of radius
(pi-w)/2. Every angle in this ball determines a strict supporting vector.

Different centres therefore have disjoint support-angle balls. The Haar
measure packing theorem on the 2*pi angle circle then gives

  sum_i (pi - w_i) <= 2*pi.
-/

namespace JSP000404Research

open Real
open scoped BigOperators
open Metric

noncomputable def angleRayDirection (theta : Real.Angle) : Plane :=
  !₂[Real.Angle.cos theta, Real.Angle.sin theta]

@[simp]
theorem angleRayDirection_coe (theta : ℝ) :
    angleRayDirection (theta : Real.Angle) = rayDirection theta := by
  ext i
  fin_cases i <;>
    simp [angleRayDirection, rayDirection]

theorem angle_norm_eq_abs_toReal (theta : Real.Angle) :
    ‖theta‖ = |theta.toReal| := by
  rw [← Real.Angle.coe_toReal theta]
  apply (AddCircle.norm_coe_eq_abs_iff
    (p := 2 * Real.pi)
    (x := theta.toReal)
    (by positivity)).2
  have h := Real.Angle.abs_toReal_le_pi theta
  simpa [abs_of_pos Real.pi_pos] using h

theorem angle_dist_eq_abs_relative_toReal
    (theta psi : Real.Angle) :
    dist theta psi = |(theta - psi).toReal| := by
  rw [dist_eq_norm, angle_norm_eq_abs_toReal]

theorem exists_real_parameter_of_mem_angle_ball
    {left right : ℝ}
    (hlr : left < right)
    (hwidth : right - left < 2 * Real.pi)
    {theta : Real.Angle}
    (htheta :
      theta ∈
        Metric.ball
          (((left + right) / 2 : ℝ) : Real.Angle)
          ((right - left) / 2)) :
    ∃ phi : ℝ,
      left < phi ∧ phi < right ∧
      theta = (phi : Real.Angle) := by
  let mid : ℝ := (left + right) / 2
  let d : ℝ :=
    (theta - (mid : Real.Angle)).toReal
  have hdist :
      dist theta (mid : Real.Angle) <
        (right - left) / 2 := by
    simpa [mid] using htheta
  have hdabs :
      |d| < (right - left) / 2 := by
    dsimp [d]
    rw [← angle_dist_eq_abs_relative_toReal]
    exact hdist
  have hd :
      -(right - left) / 2 < d ∧
        d < (right - left) / 2 := by
    simpa [abs_lt] using hdabs
  let phi : ℝ := mid + d
  refine ⟨phi, ?_, ?_, ?_⟩
  · dsimp [phi, mid]
    linarith
  · dsimp [phi, mid]
    linarith
  · have hdcoe :
        (d : Real.Angle) =
          theta - (mid : Real.Angle) := by
      dsimp [d]
      exact Real.Angle.coe_toReal _
    dsimp [phi]
    rw [Real.Angle.coe_add, hdcoe]
    abel

noncomputable def signedSupportAngle
    (sigma : Bool) (phi : ℝ) : Real.Angle :=
  if sigma then (phi : Real.Angle)
  else ((phi + Real.pi : ℝ) : Real.Angle)

theorem angleRayDirection_signedSupportAngle
    (sigma : Bool) (phi : ℝ) :
    angleRayDirection (signedSupportAngle sigma phi) =
      signedRayDirection sigma phi := by
  cases sigma <;>
    simp [signedSupportAngle, angleRayDirection_coe,
      signedRayDirection, rayDirection_add_pi]

noncomputable def supportAngleCenter
    (sigma : Bool) (a width : ℝ) : Real.Angle :=
  let left := supportParamLeft a width
  let right := supportParamRight a
  signedSupportAngle sigma ((left + right) / 2)

def supportAngleRadius (width : ℝ) : ℝ :=
  (Real.pi - width) / 2

def supportAngleBall
    (sigma : Bool) (a width : ℝ) : Set Real.Angle :=
  Metric.ball (supportAngleCenter sigma a width)
    (supportAngleRadius width)

theorem exists_support_parameter_of_mem_supportAngleBall
    {sigma : Bool} {a width : ℝ}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width < Real.pi)
    {theta : Real.Angle}
    (htheta : theta ∈ supportAngleBall sigma a width) :
    ∃ phi : ℝ,
      supportParamLeft a width < phi ∧
      phi < supportParamRight a ∧
      angleRayDirection theta =
        signedRayDirection sigma phi := by
  let left := supportParamLeft a width
  let right := supportParamRight a
  have hlr : left < right := by
    dsimp [left, right, supportParamLeft, supportParamRight]
    linarith
  have hspan :
      right - left = Real.pi - width := by
    dsimp [left, right]
    exact support_param_width a width
  have hshort : right - left < 2 * Real.pi := by
    rw [hspan]
    linarith [Real.pi_pos]
  cases hsigma : sigma with
  | false =>
      have hball :
          theta ∈
            Metric.ball
              ((((left + Real.pi) + (right + Real.pi)) / 2 : ℝ) :
                Real.Angle)
              (((right + Real.pi) - (left + Real.pi)) / 2) := by
        simpa [supportAngleBall, supportAngleCenter,
          supportAngleRadius, signedSupportAngle, hsigma,
          left, right, hspan] using htheta
      obtain ⟨psi, hpsiL, hpsiR, hthetaPsi⟩ :=
        exists_real_parameter_of_mem_angle_ball
          (left := left + Real.pi)
          (right := right + Real.pi)
          (by linarith) (by linarith [Real.pi_pos]) hball
      let phi := psi - Real.pi
      refine ⟨phi, by dsimp [phi]; linarith,
        by dsimp [phi]; linarith, ?_⟩
      rw [hthetaPsi]
      dsimp [phi]
      have hpsi : psi - Real.pi + Real.pi = psi := by ring
      rw [← hpsi, angleRayDirection_coe,
        rayDirection_add_pi]
      simp [signedRayDirection, hsigma]
  | true =>
      have hball :
          theta ∈
            Metric.ball
              ((((left + right) / 2 : ℝ)) : Real.Angle)
              ((right - left) / 2) := by
        simpa [supportAngleBall, supportAngleCenter,
          supportAngleRadius, signedSupportAngle, hsigma,
          left, right, hspan] using htheta
      obtain ⟨phi, hphiL, hphiR, hthetaPhi⟩ :=
        exists_real_parameter_of_mem_angle_ball
          (left := left) (right := right)
          hlr hshort hball
      refine ⟨phi, hphiL, hphiR, ?_⟩
      rw [hthetaPhi, angleRayDirection_coe]
      simp [signedRayDirection, hsigma]

theorem supportAngleBall_strictly_supports
    {V : Type*} {p : V → Plane}
    {i : V} {a width : ℝ}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width < Real.pi)
    (sigma : Bool)
    (hrepr : ∀ j, j ≠ i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + width ∧
        p j - p i =
          rho • signedRayDirection sigma theta) :
    ∀ theta ∈ supportAngleBall sigma a width,
      StrictSupportsAt p i (angleRayDirection theta) := by
  intro theta htheta
  obtain ⟨phi, hphiLo, hphiHi, hdir⟩ :=
    exists_support_parameter_of_mem_supportAngleBall
      hwidth0 hwidthpi htheta
  rw [hdir]
  exact strictSupportsAt_of_common_signed_interval_parameter
    hwidth0 hwidthpi sigma hphiLo hphiHi hrepr

theorem supportAngleBalls_disjoint_of_ne
    {V : Type*} {p : V → Plane}
    {i j : V} (hij : i ≠ j)
    {ai wi aj wj : ℝ}
    (hwi0 : 0 ≤ wi) (hwipi : wi < Real.pi)
    (hwj0 : 0 ≤ wj) (hwjpi : wj < Real.pi)
    (sigmai sigmaj : Bool)
    (hrepri : ∀ k, k ≠ i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        ai ≤ theta ∧ theta ≤ ai + wi ∧
        p k - p i =
          rho • signedRayDirection sigmai theta)
    (hreprj : ∀ k, k ≠ j →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        aj ≤ theta ∧ theta ≤ aj + wj ∧
        p k - p j =
          rho • signedRayDirection sigmaj theta) :
    Disjoint
      (supportAngleBall sigmai ai wi)
      (supportAngleBall sigmaj aj wj) := by
  rw [Set.disjoint_left]
  intro theta hti htj
  exact no_common_strict_support hij
    (supportAngleBall_strictly_supports
      hwi0 hwipi sigmai hrepri theta hti)
    (supportAngleBall_strictly_supports
      hwj0 hwjpi sigmaj hreprj theta htj)

theorem strict_support_arc_width_sum_le_two_pi
    {V I : Type*} [Fintype I]
    {p : V → Plane}
    (centre : I → V)
    (hcentre : Function.Injective centre)
    (a width : I → ℝ)
    (sigma : I → Bool)
    (hwidth0 : ∀ i, 0 ≤ width i)
    (hwidthpi : ∀ i, width i < Real.pi)
    (hrepr : ∀ i k, k ≠ centre i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        a i ≤ theta ∧ theta ≤ a i + width i ∧
        p k - p (centre i) =
          rho • signedRayDirection (sigma i) theta) :
    (∑ i, (Real.pi - width i)) ≤ 2 * Real.pi := by
  let S : I → Set DirectionCircle :=
    fun i => supportAngleBall (sigma i) (a i) (width i)
  have hdisj :
      PairwiseDisjoint (Set.univ : Set I) S := by
    intro i _ j _ hij
    apply supportAngleBalls_disjoint_of_ne
      (hcentre.ne hij)
      (hwidth0 i) (hwidthpi i)
      (hwidth0 j) (hwidthpi j)
      (sigma i) (sigma j)
      (hrepr i) (hrepr j)
  apply directionCircle_disjoint_ball_length_sum_le
    (center := fun i =>
      supportAngleCenter (sigma i) (a i) (width i))
    (length := fun i => Real.pi - width i)
  · intro i
    linarith [hwidthpi i]
  · intro i
    have hw0 := hwidth0 i
    linarith [Real.pi_pos]
  · simpa [S, supportAngleBall, supportAngleRadius] using hdisj

#print axioms angle_norm_eq_abs_toReal
#print axioms exists_real_parameter_of_mem_angle_ball
#print axioms supportAngleBall_strictly_supports
#print axioms supportAngleBalls_disjoint_of_ne
#print axioms strict_support_arc_width_sum_le_two_pi

end JSP000404Research
