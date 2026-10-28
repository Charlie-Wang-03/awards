import JSP000404Research.PlanarLowSupportCardinalityPacking
import JSP000404Research.ThreeFiveSaturatedUnitQuotients
import JSP000404Research.GeneralSaturatedZeroGapBudget
import Mathlib.Tactic

/-!
# Seven original centres in the whole n=3 lower strip force a triple-unit core

For EVERY 0<=delta<1/2 and t=3+delta, genuine planar AngleCap
geometry with seven or more ORIGINAL points cannot have local positive
quotient support <=2 at ALL centres: the independent strict-transition
arc packing lemma would bound #centres <=2*n=6.

At least one ACTUAL centre therefore has support >=3. The original
n=3 quotient sum bound immediately forces a RIGID exact structure:
  k=0, support=3, quotient sum=3,
  every positive quotient is ONE, and precisely three units occur.
Furthermore, the sum of ALL zero-quotient scaled projective gaps
at that centre uses at most the SINGLE strip-remainder delta budget.

This is a true, unconditional geometric NECESSARY condition for the
still-open n=3, positive-delta large-centre regime. It does NOT rule
out the triple-unit motif or supply the missing all-source payment.
-/

namespace JSP000404Research
open scoped BigOperators

/-- Every genuine n=3, >=7-point AngleCap configuration in the
ENTIRE lower half-strip has an ORIGINAL exponent-zero centre with
exactly three unit-positive quotient gaps and a SINGLE aggregate
delta budget for ALL zero-quotient gaps. -/
theorem planar_three_seven_centres_force_saturated_triple_unit_and_slack
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ}
    (hcap : AngleCap p lam)
    (hcard : 7 ≤ Fintype.card V)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (3 : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C : ∀ i : V, CentreProjectiveCycle hp i) :
    ∃ i : V,
      centreExponent (C i) t = 0 ∧
      positiveSupport (centreQuotient (C i) t) = 3 ∧
      (∑ r, centreQuotient (C i) t r) = 3 ∧
      (∀ r, centreQuotient (C i) t r ≤ 1) ∧
      unitSupport (centreQuotient (C i) t) = 3 ∧
      (∑ r ∈ (Finset.univ.filter
        (fun r : Fin (C i).gaps.length =>
          centreQuotient (C i) t r = 0)),
        t * (C i).gaps.get r) ≤ delta := by
  classical
  have hexists :
      ∃ i : V, 3 ≤ positiveSupport (centreQuotient (C i) t) := by
    by_contra hnone
    have hlow :
        ∀ i : V, positiveSupport (centreQuotient (C i) t) ≤ 2 := by
      intro i
      by_contra hlarge
      have hthree : 3 ≤ positiveSupport (centreQuotient (C i) t) := by
        omega
      exact hnone ⟨i, hthree⟩
    have hbudget :
        Fintype.card V ≤ 2 * (3 : ℕ) :=
      planar_low_support_all_centres_card_le_two_n
        hp hcap (by decide : 1 ≤ (3 : ℕ))
        hdelta0 hdeltaHalf ht hlam C hlow
    omega
  obtain ⟨i, hthree⟩ := hexists
  obtain ⟨hk, hsup, hmass⟩ :=
    three_scale_high_support_exact_rigidity
      (C i) hdelta0 hdeltaHalf ht hthree
  obtain ⟨hunitBound, hunitCount⟩ :=
    three_scale_support_three_all_unit_quotients
      (C i) hdelta0 hdeltaHalf ht hthree
  have hzeroTotal :=
    saturated_centre_zero_gap_total_le_slack
      (C i) 3 hdelta0 ht hmass
  exact ⟨i, hk, hsup, hmass, hunitBound, hunitCount, hzeroTotal⟩

#print axioms planar_three_seven_centres_force_saturated_triple_unit_and_slack

end JSP000404Research
