import Mathlib.Tactic

/-!
# Phase-cover arithmetic for the lower branch

This file isolates two elementary integer consequences behind the prospective
rotating-phase proof.

If 0 <= delta < 1/2 and intervals of normalized length at most delta cover a
circle of circumference n+delta, then any count m whose total available length
m*delta reaches n+delta must satisfy m >= 2*n+2.

Conversely, if an integer hull size h satisfies h <= 2*(n+delta), then the same
small-delta condition forces h <= 2*n.

No geometric covering or convex-hull assertion is made here; only the arithmetic
outlets are formalized.
-/

namespace JSP000404Research

/-- Cover-count arithmetic: m intervals of length at most delta cannot cover
normalized circumference n+delta unless m >= 2*n+2. -/
theorem phase_cover_count_lower
    {n m : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hcover : (n : ℝ) + delta ≤ (m : ℝ) * delta) :
    2 * n + 2 ≤ m := by
  by_contra hnot
  have hm : m ≤ 2 * n + 1 := by omega
  have hmR : (m : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hm
  have hmul :
      (m : ℝ) * delta ≤ (2 * (n : ℝ) + 1) * delta := by
    exact mul_le_mul_of_nonneg_right hmR hdelta0
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hstrict :
      (2 * (n : ℝ) + 1) * delta < (n : ℝ) + delta := by
    have htwo : 2 * delta < 1 := by linarith
    nlinarith
  linarith

/-- Integer hull-count arithmetic: h <= 2(n+delta), delta<1/2 implies h<=2n. -/
theorem hull_count_upper
    {n h : ℕ} {delta : ℝ}
    (hdelta : delta < (1 : ℝ) / 2)
    (hhull : (h : ℝ) ≤ 2 * ((n : ℝ) + delta)) :
    h ≤ 2 * n := by
  by_contra hnot
  have hh : 2 * n + 1 ≤ h := by omega
  have hhR : 2 * (n : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast hh
  have hstrict : 2 * ((n : ℝ) + delta) < 2 * (n : ℝ) + 1 := by
    linarith
  linarith

/-- Combined contradiction form used by a future phase-cover/hull injection. -/
theorem phase_cover_hull_count_contradiction
    {n m h : ℕ} {delta : ℝ}
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta < (1 : ℝ) / 2)
    (hcover : (n : ℝ) + delta ≤ (m : ℝ) * delta)
    (hhull : (h : ℝ) ≤ 2 * ((n : ℝ) + delta))
    (hinj_count : m ≤ h) :
    False := by
  have hm := phase_cover_count_lower hn hdelta0 hdelta hcover
  have hh := hull_count_upper hdelta hhull
  omega

#print axioms phase_cover_count_lower
#print axioms hull_count_upper
#print axioms phase_cover_hull_count_contradiction

end JSP000404Research
