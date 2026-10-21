import JSP000404Research.ThreeFiveTopLowSupportPacking
import JSP000404Research.CentreExponentBounds
import Mathlib.Tactic

/-!
# Exact quotient mass at high-support n=3 centres

A genuine planar centre at scale t=3+delta, 0<=delta<1/2,
has quotient sum at most three.  Since quotient sum equals
centre exponent plus positive quotient support, support >=3 forces:
  support = 3, exponent = 0, quotient sum = 3.

Combining this with five-centre transition packing narrows the
remaining n=3 top-plus-next overweight motif further: at least
one of the three low-exponent companions has this exact profile.
The actual geometric nonrealizability of that profile is NOT proved.
-/

namespace JSP000404Research

open scoped BigOperators

theorem three_scale_high_support_exact_rigidity
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {delta t : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hsupport : 3 ≤ positiveSupport (centreQuotient C t)) :
    centreExponent C t = 0 ∧
    positiveSupport (centreQuotient C t) = 3 ∧
    (∑ r, centreQuotient C t r) = 3 := by
  let q := centreQuotient C t
  have hdelta1 : delta < 1 := by linarith
  have hsum : (∑ r, q r) ≤ 3 :=
    centreQuotient_function_sum_le_n
      C 3 delta t (by omega : 1 ≤ (3 : ℕ))
      hdelta0 hdelta1 ht
  have hid : centreExponent C t + positiveSupport q =
      ∑ r, q r := by
    unfold centreExponent
    exact floorExcess_add_positiveSupport q
  have he : centreExponent C t = 0 := by
    have hs : 3 ≤ positiveSupport q := hsupport
    omega
  have hcount : positiveSupport q = 3 := by
    have hs : 3 ≤ positiveSupport q := hsupport
    omega
  have hfull : (∑ r, q r) = 3 := by omega
  exact ⟨he, hcount, hfull⟩

theorem top_next_three_exact_support_three_companion
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    {s a b c d : V}
    (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hsd : s ≠ d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (Cs : CentreProjectiveCycle hp s)
    (Ca : CentreProjectiveCycle hp a)
    (Cb : CentreProjectiveCycle hp b)
    (Cc : CentreProjectiveCycle hp c)
    (Cd : CentreProjectiveCycle hp d)
    (hs : centreExponent Cs t = 2)
    (ha : centreExponent Ca t = 1) :
    (centreExponent Cb t = 0 ∧
      positiveSupport (centreQuotient Cb t) = 3 ∧
      (∑ r, centreQuotient Cb t r) = 3) ∨
    (centreExponent Cc t = 0 ∧
      positiveSupport (centreQuotient Cc t) = 3 ∧
      (∑ r, centreQuotient Cc t r) = 3) ∨
    (centreExponent Cd t = 0 ∧
      positiveSupport (centreQuotient Cd t) = 3 ∧
      (∑ r, centreQuotient Cd t r) = 3) := by
  rcases top_next_three_companions_one_support_ge_three
    hp hcap hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hsd hab hac had hbc hbd hcd
    Cs Ca Cb Cc Cd hs ha with hb | hc | hd
  · left
    exact three_scale_high_support_exact_rigidity Cb
      hdelta0 hdeltaHalf ht hb
  · right; left
    exact three_scale_high_support_exact_rigidity Cc
      hdelta0 hdeltaHalf ht hc
  · right; right
    exact three_scale_high_support_exact_rigidity Cd
      hdelta0 hdeltaHalf ht hd

#print axioms three_scale_high_support_exact_rigidity
#print axioms top_next_three_exact_support_three_companion

end JSP000404Research
