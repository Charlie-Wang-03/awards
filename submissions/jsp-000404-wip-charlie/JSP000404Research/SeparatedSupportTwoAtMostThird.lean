import JSP000404Research.SeparatedSupportTwoSixPlusStrict
import Mathlib.Tactic

/-!
# No sharp-top double-zero quotient endpoints throughout delta ≤ 1/3

For delta < 1/3 the previously proved original-plane zero-mass
budget already contradicts the existence of two zero endpoints,
regardless of the number of centres. At delta = 1/3, original
AngleCap strict angle positivity and at least six centres exclude
the remaining degenerate case. No global TRUE-hole or surplus
payment is asserted here.
-/

namespace JSP000404Research

/-- Below the critical threshold, the quantitative geometric budget
itself rules out both top-adjacent quotient gaps being zero. -/
theorem separated_support_two_no_double_zero_of_delta_lt_third
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaThird : delta < (1 : ℝ) / 3)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (Cfam top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (Cfam i) t = n - 3)
    (hsupport : positiveSupport (centreQuotient (Cfam i) t) = 2) :
    ∃ (k : ℕ) (r : OtherVertex i) (rest : List (OtherVertex i))
      (qFirst qLast : ℕ) (qmid : List ℕ),
      (Cfam i).rays.rotate k =
        (⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t (Cfam i).gaps).rotate k =
        qFirst :: qmid ++ [qLast] ∧
      ¬ (qFirst = 0 ∧ qLast = 0) := by
  have hdeltaHalf : delta < (1 : ℝ) / 2 := by linarith
  obtain ⟨k, r, rest, qFirst, qLast, qmid, hrays, hquot, hbudget⟩ :=
    separated_support_two_double_zero_middle_angle_budget
      hp hcap Cfam hn hdelta0 hdeltaHalf ht hlam
      top hTop hit hI hsupport
  refine ⟨k, r, rest, qFirst, qLast, qmid, hrays, hquot, ?_⟩
  intro hends
  have hthirdNecessary := (hbudget hends).2
  linarith

/-- The geometric double-zero endpoint obstruction is valid on the
entire closed parameter interval 0 ≤ delta ≤ 1/3, with at least
six original centres (only the endpoint delta=1/3 needs this size). -/
theorem separated_support_two_at_least_six_no_double_zero_of_delta_le_third
    {V : Type*} [LinearOrder V] [Fintype V] [DecidableEq V]
    {p : V → Plane} (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (Cfam : ∀ v : V, CentreProjectiveCycle hp v)
    (hSixPlus : 6 ≤ Fintype.card V)
    (hn : 5 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaThird : delta ≤ (1 : ℝ) / 3)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (top : V)
    (hTop : centreExponent (Cfam top) t = n - 1)
    {i : V}
    (hit : i ≠ top)
    (hI : centreExponent (Cfam i) t = n - 3)
    (hsupport : positiveSupport (centreQuotient (Cfam i) t) = 2) :
    ∃ (k : ℕ) (r : OtherVertex i) (rest : List (OtherVertex i))
      (qFirst qLast : ℕ) (qmid : List ℕ),
      (Cfam i).rays.rotate k =
        (⟨top, hit.symm⟩ : OtherVertex i) :: r :: rest ∧
      (quotientList t (Cfam i).gaps).rotate k =
        qFirst :: qmid ++ [qLast] ∧
      ¬ (qFirst = 0 ∧ qLast = 0) := by
  by_cases hlt : delta < (1 : ℝ) / 3
  · exact separated_support_two_no_double_zero_of_delta_lt_third
      hp hcap Cfam hn hdelta0 hlt ht hlam
      top hTop hit hI hsupport
  · have heq : delta = (1 : ℝ) / 3 := by linarith
    exact separated_support_two_at_least_six_centres_no_double_zero_at_third
      hp hcap Cfam hSixPlus hn heq ht hlam
      top hTop hit hI hsupport

#print axioms separated_support_two_no_double_zero_of_delta_lt_third
#print axioms separated_support_two_at_least_six_no_double_zero_of_delta_le_third

end JSP000404Research
