import JSP000404Research.SharpCentre
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Projective direction intervals

A nonzero planar ray can be represented by a positive scalar times one of the
two signs of a unit direction `(cos theta, sin theta)`.  If all rays from a
centre admit such representatives with their parameters in one real interval
of width `w <= pi`, then every pair is projectively `w`-close: depending
on the two signs, either the genuine angle or its supplement is at most `w`.

This isolates the Euclidean geometry needed by the `ell = 1 -> SharpAt`
bridge.  The still-open cyclic-gap step only has to construct the common
projective interval.
-/

namespace JSP000404Research

open Real

/-- Unit vector at ordinary direction parameter `theta`. -/
noncomputable def rayDirection (theta : ℝ) : Plane :=
  !₂[Real.cos theta, Real.sin theta]

theorem norm_rayDirection (theta : ℝ) :
    ‖rayDirection theta‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [rayDirection, Fin.sum_univ_two]

theorem inner_rayDirection (theta phi : ℝ) :
    inner ℝ (rayDirection theta) (rayDirection phi) =
      Real.cos (theta - phi) := by
  simp [rayDirection, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub,
    mul_comm]

/-- Exact angle between two direction vectors when their parameter difference
lies in `[-pi,pi]`. -/
theorem angle_rayDirection
    (theta phi : ℝ) (hdiff : |theta - phi| ≤ Real.pi) :
    InnerProductGeometry.angle (rayDirection theta) (rayDirection phi) =
      |theta - phi| := by
  unfold InnerProductGeometry.angle
  rw [norm_rayDirection, norm_rayDirection, mul_one, div_one,
    inner_rayDirection, ← Real.cos_abs]
  exact Real.arccos_cos (abs_nonneg _) hdiff

/-- A choice of orientation of a projective ray. -/
noncomputable def signedRayDirection (sigma : Bool) (theta : ℝ) : Plane :=
  if sigma then rayDirection theta else -rayDirection theta

/-- If the underlying projective parameters are `width`-close, then either
the genuine angle or its supplement is `width`-small, independently of the
two signs. -/
theorem signedRay_projective_close
    {theta phi width : ℝ}
    (hwidth0 : 0 ≤ width)
    (hdiff : |theta - phi| ≤ width)
    (hwidthpi : width ≤ Real.pi)
    (sigma tau : Bool) :
    InnerProductGeometry.angle
        (signedRayDirection sigma theta)
        (signedRayDirection tau phi) ≤ width ∨
      Real.pi -
        InnerProductGeometry.angle
          (signedRayDirection sigma theta)
          (signedRayDirection tau phi) ≤ width := by
  have hpi : |theta - phi| ≤ Real.pi := hdiff.trans hwidthpi
  have hang := angle_rayDirection theta phi hpi
  cases sigma <;> cases tau
  · left
    change InnerProductGeometry.angle
      (-rayDirection theta) (-rayDirection phi) ≤ width
    rw [InnerProductGeometry.angle_neg_neg, hang]
    exact hdiff
  · right
    change Real.pi -
      InnerProductGeometry.angle (-rayDirection theta) (rayDirection phi) ≤ width
    rw [InnerProductGeometry.angle_neg_left, hang]
    linarith
  · right
    change Real.pi -
      InnerProductGeometry.angle (rayDirection theta) (-rayDirection phi) ≤ width
    rw [InnerProductGeometry.angle_neg_right, hang]
    linarith
  · left
    change InnerProductGeometry.angle
      (rayDirection theta) (rayDirection phi) ≤ width
    rw [hang]
    exact hdiff

/-- Rays represented by parameters in one interval of width `width` are
uniformly projectively close at their common centre. -/
theorem projectiveCloseAt_of_signed_interval
    {V : Type*} {p : V → Plane}
    {i : V} {a width : ℝ}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width ≤ Real.pi)
    (hrepr : ∀ j, j ≠ i →
      ∃ rho : ℝ, ∃ sigma : Bool, ∃ theta : ℝ,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + width ∧
        p j - p i = rho • signedRayDirection sigma theta) :
    ∀ j k, j ≠ i → k ≠ i → j ≠ k →
      ProjectiveCloseAt p width i j k := by
  intro j k hji hki hjk
  obtain ⟨rhoj, sigmaj, thetaj, hrhoj, hjlo, hjhi, hjrepr⟩ :=
    hrepr j hji
  obtain ⟨rhok, sigmak, thetak, hrhok, hklo, hkhi, hkrepr⟩ :=
    hrepr k hki
  have hdiff : |thetaj - thetak| ≤ width := by
    rw [abs_le]
    constructor <;> linarith
  have hproj :=
    signedRay_projective_close hwidth0 hdiff hwidthpi sigmaj sigmak
  unfold ProjectiveCloseAt
  change
    InnerProductGeometry.angle (p j - p i) (p k - p i) ≤ width ∨
      Real.pi - InnerProductGeometry.angle (p j - p i) (p k - p i) ≤ width
  rw [hjrepr, hkrepr,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hrhoj,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hrhok]
  exact hproj

/-- Final geometric half of the sharp-centre bridge: once the rays at a centre
fit in a projective interval of width `delta * lam`, the global angle cap
turns projective closeness into the genuine `SharpAt` bound. -/
theorem sharpAt_of_signed_interval
    {V : Type*} {p : V → Plane}
    {i : V} {a delta lam : ℝ}
    (hcap : AngleCap p lam)
    (hwidth0 : 0 ≤ delta * lam)
    (hwidthpi : delta * lam ≤ Real.pi)
    (hsmall : delta * lam < lam)
    (hrepr : ∀ j, j ≠ i →
      ∃ rho : ℝ, ∃ sigma : Bool, ∃ theta : ℝ,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + delta * lam ∧
        p j - p i = rho • signedRayDirection sigma theta) :
    SharpAt p delta lam i := by
  apply sharpAt_of_projective_close hcap hsmall
  exact projectiveCloseAt_of_signed_interval
    hwidth0 hwidthpi hrepr

#print axioms norm_rayDirection
#print axioms inner_rayDirection
#print axioms angle_rayDirection
#print axioms signedRay_projective_close
#print axioms projectiveCloseAt_of_signed_interval
#print axioms sharpAt_of_signed_interval

end JSP000404Research
