import JSP000404Research.HighExponentTransitionPacking
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# The top nontrivial exponent forces a single positive quotient gap

If a concrete centre has exponent n-1 while the quotient mass is
at most n, its positive quotient support MUST be exactly one.
Thus any actual high-exponent transition certificate at that centre
has transition quotient exactly n.

This is a sharpened top-centre fact with no new geometric
hypotheses and no admission. It supplies a missing arithmetic
component for the five-exposed-centres obstruction.
-/

namespace JSP000404Research

/-- A concrete top centre in the lower Sendov regime necessarily
has exactly one positive quotient position. -/
theorem top_exponent_positiveSupport_eq_one
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 1) :
    positiveSupport (centreQuotient C t) = 1 := by
  let q := centreQuotient C t
  have hsum : (∑ r, q r) ≤ n :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega : 1 ≤ n) hdelta0 hdelta1 ht
  have hnozero : positiveSupport q ≠ 0 := by
    intro hz
    have hq0 := positiveSupport_eq_zero_imp q hz
    have hk0 : centreExponent C t = 0 := by
      unfold centreExponent floorExcess
      simp [q, hq0]
    omega
  have hid := floorExcess_add_positiveSupport q
  have hcount : centreExponent C t + positiveSupport q ≤ n := by
    unfold centreExponent
    rw [hid]
    exact hsum
  omega

/-- At a top centre, every actual high-exponent transition
certificate carries a quotient gap of the full value n. -/
theorem top_exponent_transition_qe_eq_n
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {t delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hexp : centreExponent C t = n - 1)
    (H : HighExponentTransitionIntervalCertificate hp t i C) :
    H.qe = n := by
  have hs := top_exponent_positiveSupport_eq_one
    C hn hdelta0 hdelta1 ht hexp
  have hqe :=
    highTransition_qe_eq_exponent_add_one_of_support_one
      C H hs
  rw [hexp] at hqe
  omega

#print axioms top_exponent_positiveSupport_eq_one
#print axioms top_exponent_transition_qe_eq_n

end JSP000404Research
