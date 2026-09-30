import JSP000404Research.ResidualHardRemainder
import JSP000404Research.PlanarStandardResidualBudget
import Mathlib.Tactic

/-!
# Hard residual accounting with an explicit unpaid slack

The lower-branch hard-remainder theorem requires all hard words to fit in the
Boolean holes. For the upper Sendov branch we only need the weaker target

  sum_v 2^(exponent v) <= 2^n + 2^(n-2).

The same exact residual accounting proves a general slack version:

  hardCost <= holes + slack
  =>
  targetMass <= 2^n + slack.

Thus the two Sendov branches share one residual framework. The lower branch
uses zero slack, while the upper branch uses 2^(n-2).
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

theorem exponent_capacity_of_hard_words_fit_holes_with_slack
    {V : Type*} [LinearOrder V] [Fintype V] {n slack : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpay :
      (saturatedOverlapWords C exponent).card +
          (lossCompletionWords C exponent).card
        ≤
      (2 ^ n - (coveredCompletionWords C).card) + slack) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n + slack := by
  have hcovered :
      (coveredCompletionWords C).card ≤ 2 ^ n :=
    coveredCompletionWords_card_le_two_pow C
  have hstrict :=
    strictStrictOverlap_card_le_total_surplus C exponent
  have hsplit :=
    saturatedOverlap_card_add_strict_eq_overlap C exponent
  have hloss :=
    lossCompletionWords_card_eq_totalDyadicProfileLoss
      C exponent hexp honeLoss
  have hproject0 :=
    projectedFree_mass_eq_covered_add_overlap C
  have hproject :
      (∑ v, 2 ^ projectedFree C v) =
        (coveredCompletionWords C).card +
          (overlapCompletionWords C).card := by
    simpa [projectedFree] using hproject0
  have hbalance :=
    residual_projection_accounting_balance
      exponent (projectedFree C)
      (coveredCompletionWords C).card
      (overlapCompletionWords C).card
      hproject
  rw [hloss] at hpay
  omega

/-- The upper-branch constant is exactly the general slack outlet with
slack equal to 2^(n-2). -/
theorem exponent_capacity_of_upper_branch_hard_defect
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hpay :
      (saturatedOverlapWords C exponent).card +
          (lossCompletionWords C exponent).card
        ≤
      (2 ^ n - (coveredCompletionWords C).card) +
        2 ^ (n - 2)) :
    (∑ v, 2 ^ exponent v) ≤
      2 ^ n + 2 ^ (n - 2) :=
  exponent_capacity_of_hard_words_fit_holes_with_slack
    C exponent hexp honeLoss hpay

#print axioms exponent_capacity_of_hard_words_fit_holes_with_slack
#print axioms exponent_capacity_of_upper_branch_hard_defect

end OrderedEdgeColoring

namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData
open scoped BigOperators

/-- Arbitrary-cardinality planar upper-branch capacity, reduced to allowing at
most 2^(n-2) unmatched hard residual words. -/
theorem planar_upperBranch_capacity_of_quarter_hard_defect
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (C :
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hpay :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t :=
        sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
      let D :=
        genericDirectionData_sendov hp hcap htpos hlam
      let hwidth : t < (n + 1 : ℕ) := by
        rw [ht]
        exact_mod_cast
          (show (n : ℝ) + delta < (n : ℝ) + 1 by linarith)
      let B :=
        standardResidualColoring D n hwidth
      let exponent : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (C i) t
      (saturatedOverlapWords B exponent).card +
          (lossCompletionWords B exponent).card
        ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        2 ^ (n - 2)) :
    ∑ i : ProjectionOrdered V, 2 ^ centreExponent (C i) t
      ≤ 2 ^ n + 2 ^ (n - 2) := by
  letI : LinearOrder (ProjectionOrdered V) :=
    projectionLinearOrder hp
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hwidthR : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  have hwidth : t < (n + 1 : ℕ) := by
    exact_mod_cast hwidthR

  let D :=
    genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n hwidth
  let exponent : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (C i) t

  have hexp : ∀ i, exponent i ≤ n := by
    intro i
    exact Nat.le_of_lt
      (centreExponent_lt_n
        (C i) n delta t (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht)

  have honeLoss :
      ∀ i, (active B i).card ≤ n - exponent i + 1 := by
    intro i
    simpa [B, D, exponent] using
      planarStandardResidual_active_card_le_oneLayer
        hp hcap (by omega : 1 ≤ n)
        hdelta0 hdelta1 ht hlam i (C i)

  have hpay' :
      (saturatedOverlapWords B exponent).card +
          (lossCompletionWords B exponent).card
        ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        2 ^ (n - 2) := by
    simpa [B, D, exponent] using hpay

  have hcap' :=
    exponent_capacity_of_upper_branch_hard_defect
      B exponent hexp honeLoss hpay'
  simpa [exponent] using hcap'

#print axioms planar_upperBranch_capacity_of_quarter_hard_defect

end ProjectionOrdered
end JSP000404Research
