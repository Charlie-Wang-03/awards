import JSP000404Research.CentreExponent
import JSP000404Research.SharpDeficit
import Mathlib.Tactic

/-!
# General upper bound for a concrete centre exponent

At fixed Sendov scale t=n+delta with 0<=delta<1, the concrete quotient mass
satisfies sum q <= n.

Since

  floorExcess(q) + positiveSupport(q) = sum q,

either the positive support vanishes, in which case every quotient and the
exponent vanish, or the support is at least one and the exponent is at most
n-1.

Hence every actual nontrivial centre exponent is strictly below n.
-/

namespace JSP000404Research

open scoped BigOperators

theorem centreExponent_lt_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    centreExponent C t < n := by
  let q := centreQuotient C t
  have hsum : (∑ r, q r) ≤ n := by
    exact centreQuotient_function_sum_le_n
      C n delta t hn hdelta0 hdelta1 ht
  have hid := floorExcess_add_positiveSupport q
  by_cases hs : positiveSupport q = 0
  · have hq0 := positiveSupport_eq_zero_imp q hs
    have hk0 : centreExponent C t = 0 := by
      unfold centreExponent floorExcess
      simp [q, hq0]
    rw [hk0]
    omega
  · have hs1 : 1 ≤ positiveSupport q :=
      Nat.one_le_iff_ne_zero.mpr hs
    have hk :
        centreExponent C t + positiveSupport q ≤ n := by
      unfold centreExponent
      rw [hid]
      exact hsum
    omega

/-- Equivalent weak upper bound used by arithmetic terminals. -/
theorem centreExponent_le_n_sub_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (n : ℕ) (delta t : ℝ)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta) :
    centreExponent C t ≤ n - 1 := by
  have h :=
    centreExponent_lt_n C n delta t
      hn hdelta0 hdelta1 ht
  omega

#print axioms centreExponent_lt_n
#print axioms centreExponent_le_n_sub_one

end JSP000404Research
