
import JSP000404Research.ProjectionHalfPlaneAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-!
# Argument order in the open right half-plane

For z with positive real part, the principal argument lies in
(-pi/2,pi/2).  On this interval tangent is injective, and

  tan(arg z) = im(z)/re(z).

Hence

  arg z = arctan(im(z)/re(z)).

The slope of z+w, when both real parts are positive, is a positive weighted
average of the two slopes.  Therefore the argument of z+w lies between the
arguments of z and w.

This is the exact analytic lemma needed for the triangle-betweenness field of
ForwardAngleLift.
-/

namespace JSP000404Research

open Real Complex

noncomputable def complexSlope (z : ℂ) : ℝ :=
  z.im / z.re

theorem arg_eq_arctan_complexSlope_of_re_pos
    {z : ℂ}
    (hz : 0 < z.re) :
    z.arg = Real.arctan (complexSlope z) := by
  have harg :
      -(Real.pi / 2) < z.arg ∧
        z.arg < Real.pi / 2 := by
    have habs :
        |z.arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl hz)
    simpa [abs_lt] using habs
  have htan :
      Real.arctan (Real.tan z.arg) = z.arg :=
    Real.arctan_tan harg.1 harg.2
  rw [Complex.tan_arg] at htan
  simpa [complexSlope] using htan.symm

theorem complexSlope_le_iff_arg_le_of_re_pos
    {z w : ℂ}
    (hz : 0 < z.re)
    (hw : 0 < w.re) :
    complexSlope z ≤ complexSlope w ↔
      z.arg ≤ w.arg := by
  rw [arg_eq_arctan_complexSlope_of_re_pos hz,
      arg_eq_arctan_complexSlope_of_re_pos hw]
  exact Real.arctan_le_arctan_iff.symm

/-- If slope(z) <= slope(w), then slope(z+w) lies between them. -/
theorem complexSlope_add_between_of_le
    {z w : ℂ}
    (hz : 0 < z.re)
    (hw : 0 < w.re)
    (hzw : complexSlope z ≤ complexSlope w) :
    complexSlope z ≤ complexSlope (z + w) ∧
      complexSlope (z + w) ≤ complexSlope w := by
  have hsum : 0 < (z + w).re := by
    simp only [Complex.add_re]
    linarith
  have hcross :
      z.im * w.re ≤ w.im * z.re := by
    exact (div_le_div_iff₀ hz hw).1
      (by simpa [complexSlope] using hzw)
  constructor
  · apply (div_le_div_iff₀ hz hsum).2
    simp only [complexSlope, Complex.add_re, Complex.add_im]
    nlinarith
  · apply (div_le_div_iff₀ hsum hw).2
    simp only [complexSlope, Complex.add_re, Complex.add_im]
    nlinarith

/-- Unordered slope-betweenness form. -/
theorem complexSlope_add_between
    {z w : ℂ}
    (hz : 0 < z.re)
    (hw : 0 < w.re) :
    (complexSlope z ≤ complexSlope (z + w) ∧
      complexSlope (z + w) ≤ complexSlope w)
    ∨
    (complexSlope w ≤ complexSlope (z + w) ∧
      complexSlope (z + w) ≤ complexSlope z) := by
  rcases le_total (complexSlope z) (complexSlope w) with hzw | hwz
  · exact Or.inl
      (complexSlope_add_between_of_le hz hw hzw)
  · right
    have h :=
      complexSlope_add_between_of_le hw hz hwz
    simpa [add_comm] using h

/-- Argument of a sum of two right-half-plane vectors lies between their
arguments. -/
theorem arg_add_between_of_re_pos
    {z w : ℂ}
    (hz : 0 < z.re)
    (hw : 0 < w.re) :
    (z.arg ≤ (z + w).arg ∧
      (z + w).arg ≤ w.arg)
    ∨
    (w.arg ≤ (z + w).arg ∧
      (z + w).arg ≤ z.arg) := by
  have hsum : 0 < (z + w).re := by
    simp only [Complex.add_re]
    linarith
  rcases complexSlope_add_between hz hw with h | h
  · left
    constructor
    · exact
        (complexSlope_le_iff_arg_le_of_re_pos hz hsum).1 h.1
    · exact
        (complexSlope_le_iff_arg_le_of_re_pos hsum hw).1 h.2
  · right
    constructor
    · exact
        (complexSlope_le_iff_arg_le_of_re_pos hw hsum).1 h.1
    · exact
        (complexSlope_le_iff_arg_le_of_re_pos hsum hz).1 h.2

#print axioms arg_eq_arctan_complexSlope_of_re_pos
#print axioms complexSlope_add_between_of_le
#print axioms complexSlope_add_between
#print axioms arg_add_between_of_re_pos

end JSP000404Research
