import JSP000404Research.ConcreteSharpCentre
import Mathlib.Tactic

/-!
# Zero-cluster width and pairwise angle conversion

This file isolates two geometry-free / local-geometric bridges needed for the
arbitrary-cardinality support-two argument.

1. If a normalized projective cluster has total width G with

     t * G <= delta,    lambda = pi/t,

   then its physical angular width pi*G is at most delta*lambda.

2. If two actual displacement rays admit positive-radius representations with
   one common Boolean sign and parameters inside the same interval of width W
   strictly below pi, then their true Euclidean angle is at most W.

Combining these facts, once the cyclic support-two combinatorics places all
non-sharp rays in one zero-gap block, every pair of those rays makes angle at
most delta*lambda.
-/

namespace JSP000404Research

open Real

theorem pi_mul_width_le_delta_lam_of_scaled_width
    {G t delta lam : ℝ}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hG : t * G ≤ delta) :
    Real.pi * G ≤ delta * lam := by
  rw [hlam]
  have hdiv : G ≤ delta / t := by
    rw [le_div_iff₀ ht]
    simpa [mul_comm] using hG
  have hpi :=
    mul_le_mul_of_nonneg_left hdiv Real.pi_pos.le
  calc
    Real.pi * G ≤ Real.pi * (delta / t) := hpi
    _ = delta * (Real.pi / t) := by ring

/-- Pairwise version of the common-signed interval angle bound. -/
theorem angle_le_width_of_two_common_signed_reprs
    {p : V → Plane} {V : Type*}
    {i j k : V}
    {a width : ℝ} {sigma : Bool}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width < Real.pi)
    (rhoj rhok thetaj thetak : ℝ)
    (hrhoj : 0 < rhoj)
    (hrhok : 0 < rhok)
    (hjlo : a ≤ thetaj)
    (hjhi : thetaj ≤ a + width)
    (hklo : a ≤ thetak)
    (hkhi : thetak ≤ a + width)
    (hjrepr :
      p j - p i =
        rhoj • signedRayDirection sigma thetaj)
    (hkrepr :
      p k - p i =
        rhok • signedRayDirection sigma thetak) :
    EuclideanGeometry.angle (p j) (p i) (p k) ≤ width := by
  have hdiff : |thetaj - thetak| ≤ width := by
    rw [abs_le]
    constructor <;> linarith
  have hdiffpi : |thetaj - thetak| ≤ Real.pi :=
    hdiff.trans hwidthpi.le
  change
    InnerProductGeometry.angle
        (p j - p i) (p k - p i) ≤ width
  rw [hjrepr, hkrepr,
      angle_positive_smul_signedRay hrhoj hrhok]
  rw [angle_signedRayDirection_eq_of_sign_eq
      (theta := thetaj) (phi := thetak) rfl hdiffpi]
  exact hdiff

/-- Convenient interval-data form. -/
theorem angle_le_width_of_two_common_signed_interval
    {p : V → Plane} {V : Type*}
    {i j k : V}
    {a width : ℝ} {sigma : Bool}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width < Real.pi)
    (hj :
      ∃ rho theta,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + width ∧
        p j - p i =
          rho • signedRayDirection sigma theta)
    (hk :
      ∃ rho theta,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + width ∧
        p k - p i =
          rho • signedRayDirection sigma theta) :
    EuclideanGeometry.angle (p j) (p i) (p k) ≤ width := by
  obtain ⟨rhoj, thetaj, hrhoj, hjlo, hjhi, hjrepr⟩ := hj
  obtain ⟨rhok, thetak, hrhok, hklo, hkhi, hkrepr⟩ := hk
  exact angle_le_width_of_two_common_signed_reprs
    hwidth0 hwidthpi
    rhoj rhok thetaj thetak
    hrhoj hrhok hjlo hjhi hklo hkhi
    hjrepr hkrepr

/-- Delta-width specialization used by support-two zero clusters. -/
theorem angle_le_delta_lam_of_zero_cluster_interval
    {p : V → Plane} {V : Type*}
    {i j k : V}
    {a G t delta lam : ℝ} {sigma : Bool}
    (ht : 0 < t)
    (hlam : lam = Real.pi / t)
    (hG0 : 0 ≤ G)
    (hG : t * G ≤ delta)
    (hwidthpi : Real.pi * G < Real.pi)
    (hj :
      ∃ rho theta,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + Real.pi * G ∧
        p j - p i =
          rho • signedRayDirection sigma theta)
    (hk :
      ∃ rho theta,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + Real.pi * G ∧
        p k - p i =
          rho • signedRayDirection sigma theta) :
    EuclideanGeometry.angle (p j) (p i) (p k) ≤
      delta * lam := by
  have hangle :=
    angle_le_width_of_two_common_signed_interval
      (p := p) (i := i) (j := j) (k := k)
      (a := a) (width := Real.pi * G) (sigma := sigma)
      (mul_nonneg Real.pi_pos.le hG0)
      hwidthpi hj hk
  exact hangle.trans
    (pi_mul_width_le_delta_lam_of_scaled_width
      ht hlam hG)

#print axioms pi_mul_width_le_delta_lam_of_scaled_width
#print axioms angle_le_width_of_two_common_signed_reprs
#print axioms angle_le_delta_lam_of_zero_cluster_interval

end JSP000404Research
