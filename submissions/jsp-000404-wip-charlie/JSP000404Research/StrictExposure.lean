import JSP000404Research.ProjectiveInterval
import Mathlib.Tactic

/-!
# Strict exposure from one signed angular interval

Instead of invoking the full convex-hull API immediately, use the following
lightweight certificate.

A centre i is strictly exposed if there is a vector u such that every other
point lies strictly on the positive side of the line through p i orthogonal to
u:

  0 < inner u (p j - p i).

If all displacement rays from i have the same projective sign and their
parameters lie in an interval of width strictly below pi, the midpoint
direction of that interval is such a certificate.  Every ray differs from the
midpoint by less than pi/2, hence has positive inner product with it.
-/

namespace JSP000404Research

open Real

/-- A strict supporting-line certificate at a point. -/
def StrictlyExposedAt {V : Type*} (p : V → Plane) (i : V) : Prop :=
  ∃ u : Plane, ∀ j, j ≠ i → 0 < inner ℝ u (p j - p i)

/-- Same signed projective directions have the ordinary cosine inner product. -/
theorem inner_signedRayDirection_same
    (sigma : Bool) (theta phi : ℝ) :
    inner ℝ (signedRayDirection sigma theta)
        (signedRayDirection sigma phi) =
      Real.cos (theta - phi) := by
  cases sigma <;> simp [signedRayDirection, inner_rayDirection]

/-- A parameter inside an interval of width < pi differs from the midpoint by
strictly less than pi/2. -/
theorem abs_midpoint_sub_lt_pi_div_two
    {a width theta : ℝ}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width < Real.pi)
    (hlo : a ≤ theta)
    (hhi : theta ≤ a + width) :
    |(a + width / 2) - theta| < Real.pi / 2 := by
  rw [abs_lt]
  constructor <;> linarith

/-- The signed midpoint direction has positive inner product with every
same-signed ray in a strict sub-pi interval. -/
theorem inner_midpoint_signedRay_pos
    {a width theta : ℝ}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width < Real.pi)
    (hlo : a ≤ theta)
    (hhi : theta ≤ a + width)
    (sigma : Bool) :
    0 <
      inner ℝ
        (signedRayDirection sigma (a + width / 2))
        (signedRayDirection sigma theta) := by
  rw [inner_signedRayDirection_same]
  apply Real.cos_pos_of_mem_Ioo
  have h :=
    abs_midpoint_sub_lt_pi_div_two hwidth0 hwidthpi hlo hhi
  rw [abs_lt] at h
  exact h

/-- Common sign + angular interval width < pi gives a strict supporting-line
certificate. -/
theorem strictlyExposedAt_of_common_signed_interval
    {V : Type*} {p : V → Plane}
    {i : V} {a width : ℝ}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width < Real.pi)
    (sigma : Bool)
    (hrepr : ∀ j, j ≠ i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + width ∧
        p j - p i = rho • signedRayDirection sigma theta) :
    StrictlyExposedAt p i := by
  refine ⟨signedRayDirection sigma (a + width / 2), ?_⟩
  intro j hji
  obtain ⟨rho, theta, hrho, hlo, hhi, hjrepr⟩ :=
    hrepr j hji
  rw [hjrepr, inner_smul_right]
  have hinner :=
    inner_midpoint_signedRay_pos
      hwidth0 hwidthpi hlo hhi sigma
  exact mul_pos hrho hinner

#print axioms inner_signedRayDirection_same
#print axioms abs_midpoint_sub_lt_pi_div_two
#print axioms inner_midpoint_signedRay_pos
#print axioms strictlyExposedAt_of_common_signed_interval

end JSP000404Research
