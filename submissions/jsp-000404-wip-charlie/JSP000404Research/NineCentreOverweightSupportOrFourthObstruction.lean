import JSP000404Research.NineCentreTopFourthLayerCapacity
import Mathlib.Tactic

/-!
# A true nine-centre overweight obstruction: support-two/three OR six fourth-layer centres

No extra fourth-layer census hypothesis is used for THIS dichotomy.
For n>=5, <=9 original centres, a true top exponent n-1 and absent
n-2 layer, ANY overweight configuration must satisfy at least one:

1. there is an actual n-3 centre with quotient support TWO or THREE;
2. there are at least SIX actual centres of exponent n-4.

This applies both the genuine top/third support-one geometric exclusion
and the kernel-verified fourth-layer dyadic budget. It is a necessary
structural condition, not a construction of a counterexample nor a
proof of the unrestricted global six-source payment.
-/

namespace JSP000404Research

open scoped BigOperators

theorem planar_nine_overweight_support_two_three_or_six_fourth
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hcard3 : 3 ≤ Fintype.card V)
    (hcard9 : Fintype.card V ≤ 9)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (s : V)
    (hs : centreExponent (C s) t = n - 1)
    (hnoNext : ∀ i : V, centreExponent (C i) t ≠ n - 2)
    (hover : 2 ^ n < ∑ i : V, 2 ^ centreExponent (C i) t) :
    (∃ i : V, centreExponent (C i) t = n - 3 ∧
      (positiveSupport (centreQuotient (C i) t) = 2 ∨
       positiveSupport (centreQuotient (C i) t) = 3)) ∨
    5 < ((Finset.univ : Finset V).filter
      (fun i => centreExponent (C i) t = n - 4)).card := by
  classical
  by_cases hfourth :
      ((Finset.univ : Finset V).filter
        (fun i => centreExponent (C i) t = n - 4)).card ≤ 5
  · left
    by_contra hnone
    have hdelta1 : delta < 1 := by linarith
    have hThirdSupportOne :
        ∀ i : V, centreExponent (C i) t = n - 3 →
          positiveSupport (centreQuotient (C i) t) = 1 := by
      intro i hi
      rcases concrete_deficit_three_structure
          (C i) (by omega : 4 ≤ n) hdelta0 hdelta1 ht hi
        with h1 | h2 | h3
      · exact h1.1
      · exact False.elim (hnone ⟨i, hi, Or.inl h2.1⟩)
      · exact False.elim (hnone ⟨i, hi, Or.inr h3.1⟩)
    have hcapacity :=
      planar_nine_centre_top_no_next_third_support_one_fourth_at_most_five
        hp hcap hcard3 hcard9 hn hdelta0 hdeltaHalf ht hlam
        C s hs hnoNext hThirdSupportOne hfourth
    exact (not_lt_of_ge hcapacity) hover
  · right
    omega

#print axioms planar_nine_overweight_support_two_three_or_six_fourth

end JSP000404Research
