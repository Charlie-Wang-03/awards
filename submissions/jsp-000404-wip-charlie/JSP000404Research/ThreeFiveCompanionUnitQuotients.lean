import JSP000404Research.ThreeFiveSupportThreeRigidity
import Mathlib.Tactic

/-!
# All quotient entries are units in the n=3 high-support companion

The certified n=3 five-centre transition obstruction and exact
support-three rigidity imply that at least one of the three residual
centres has exponent zero, support three, total quotient three.
Since floorExcess is the sum of (q-1)_+, zero exponent forces
every integer quotient entry to be at most one.

This is an exact necessary profile (three unit positive quotients),
NOT geometric nonexistence and NOT a global source payment.
-/

namespace JSP000404Research

open scoped BigOperators

theorem floorExcess_zero_forces_unit_quotients
    {I : Type*} [Fintype I] (q : I → ℕ)
    (hzero : floorExcess q = 0) :
    ∀ i : I, q i ≤ 1 := by
  classical
  intro i
  have hterm : q i - 1 ≤ ∑ x : I, (q x - 1) :=
    Finset.single_le_sum
      (f := fun x : I => q x - 1)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  unfold floorExcess at hzero
  rw [hzero] at hterm
  omega

theorem three_scale_high_support_unit_quotients
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    {delta t : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hsupport : 3 ≤ positiveSupport (centreQuotient C t)) :
    ∀ r, centreQuotient C t r ≤ 1 := by
  have hzero := (three_scale_high_support_exact_rigidity C
    hdelta0 hdeltaHalf ht hsupport).1
  change floorExcess (centreQuotient C t) = 0 at hzero
  exact floorExcess_zero_forces_unit_quotients
    (centreQuotient C t) hzero

theorem top_next_three_has_unit_quotient_companion
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
    (positiveSupport (centreQuotient Cb t) = 3 ∧
      (∀ r, centreQuotient Cb t r ≤ 1)) ∨
    (positiveSupport (centreQuotient Cc t) = 3 ∧
      (∀ r, centreQuotient Cc t r ≤ 1)) ∨
    (positiveSupport (centreQuotient Cd t) = 3 ∧
      (∀ r, centreQuotient Cd t r ≤ 1)) := by
  rcases top_next_three_exact_support_three_companion
    hp hcap hdelta0 hdeltaHalf ht hlam
    hsa hsb hsc hsd hab hac had hbc hbd hcd
    Cs Ca Cb Cc Cd hs ha with hb | hc | hd
  · left
    refine ⟨hb.2.1, ?_⟩
    exact three_scale_high_support_unit_quotients Cb
      hdelta0 hdeltaHalf ht (by omega)
  · right; left
    refine ⟨hc.2.1, ?_⟩
    exact three_scale_high_support_unit_quotients Cc
      hdelta0 hdeltaHalf ht (by omega)
  · right; right
    refine ⟨hd.2.1, ?_⟩
    exact three_scale_high_support_unit_quotients Cd
      hdelta0 hdeltaHalf ht (by omega)

#print axioms floorExcess_zero_forces_unit_quotients
#print axioms three_scale_high_support_unit_quotients
#print axioms top_next_three_has_unit_quotient_companion

end JSP000404Research
