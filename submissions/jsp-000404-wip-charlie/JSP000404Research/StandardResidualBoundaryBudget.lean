
import JSP000404Research.BoundaryDominance
import Mathlib.Tactic

/-!
# Exact arithmetic budget for the standard residual partition

The standard residual construction keeps n ordinary unit bands and one final
short band of width delta<1.  On the projective direction circle this gives
n+1 boundary points, all consecutive spacings at most one.

Suppose b records how many of these n+1 boundaries lie in each consecutive
centre-ray gap, and q is the natural floor quotient of the same gap.

If every gap satisfies q(i)<=b(i), then BoundaryDominance at total mass n+1
gives

  positiveSupport(b)
    <= (n+1)-floorExcess(q)
    <= n-floorExcess(q)+1.

Thus the standard residual local palette is automatically within the exact
one-layer Sendov budget once the geometric boundary allocation is built.
-/

namespace JSP000404Research

open scoped BigOperators

theorem standardResidual_support_le_deficit_add_one
    {I : Type*} [Fintype I]
    (q b : I → ℕ)
    (n : ℕ)
    (hsum :
      (∑ i, b i) = n + 1)
    (hdom :
      ∀ i, q i ≤ b i) :
    positiveSupport b ≤
      n - floorExcess q + 1 := by
  have hfull :
      positiveSupport b ≤
        (n + 1) - floorExcess q :=
    support_le_deficit_of_full_domination
      q b (n + 1) hsum hdom
  omega

/-- Centre-exponent spelling of the same arithmetic statement. -/
theorem standardResidual_support_le_centreDeficit_add_one
    {I : Type*} [Fintype I]
    (q b : I → ℕ)
    (n exponent : ℕ)
    (hexponent : exponent = floorExcess q)
    (hsum :
      (∑ i, b i) = n + 1)
    (hdom :
      ∀ i, q i ≤ b i) :
    positiveSupport b ≤
      n - exponent + 1 := by
  subst exponent
  exact standardResidual_support_le_deficit_add_one
    q b n hsum hdom

#print axioms standardResidual_support_le_deficit_add_one
#print axioms standardResidual_support_le_centreDeficit_add_one

end JSP000404Research
