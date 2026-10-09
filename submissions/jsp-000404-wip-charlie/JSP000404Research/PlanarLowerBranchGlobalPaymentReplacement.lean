import JSP000404Research.PlanarCompletionDefectBalance
import JSP000404Research.ResidualCompletionAccounting
import Mathlib.Tactic

/-!
# Replacement for the refuted G1 Hall-expansion branch

An explicit 3-vertex DirectionData model proves that the proposed universal
G1 (minimal loss-free deficient cores are impossible) is FALSE, even though
the target dyadic inequality holds at equality in that same model.

The actual arithmetic outlet is global residual completion-defect payment:
  overlapMass + lossMass <= BooleanHoleMass + surplusMass.
This interface requires neither subset Hall expansion nor the false G1
property. Both implications in the equivalence below are verified by Lean.

IMPORTANT: Payment is *equivalent* to the desired dyadic capacity once
completion accounting is established. Thus this is a sound reformulation,
NOT an independent geometric proof of the still-open payment inequality.
-/

namespace JSP000404Research
namespace ProjectionOrdered

open OrderedEdgeColoring
open DirectionData

/-- Canonical planar lower-branch capacity follows directly from global
Boolean-hole/overlap/surplus payment, without using either Hall G1 or G2. -/
theorem planar_lower_branch_dyadic_capacity_of_global_payment
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i)
    (hpayment :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      let htpos : 0 < t := by
        rw [ht]
        have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
      let D := genericDirectionData_sendov hp hcap htpos hlam
      let B := standardResidualColoring D n (by exact_mod_cast hwidth)
      let k : ProjectionOrdered V → ℕ :=
        fun i => centreExponent (cycles i) t
      (overlapCompletionWords B).card +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        totalDyadicProfileSurplus k (projectedFree B)) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    (∑ i : ProjectionOrdered V,
      2 ^ centreExponent (cycles i) t) ≤ 2 ^ n := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change (∑ i : ProjectionOrdered V, 2 ^ k i) ≤ 2 ^ n
  have hpayment' :
      (overlapCompletionWords B).card +
        totalDyadicProfileLoss k (projectedFree B) ≤
      (2 ^ n - (coveredCompletionWords B).card) +
        totalDyadicProfileSurplus k (projectedFree B) := by
    exact hpayment
  exact exponent_capacity_of_completion_defect_payment B k hpayment'

/-- The replacement global-payment obligation is equivalent to the true
lower-branch target. In particular, it is not yet a discharged theorem. -/
theorem planar_lower_branch_dyadic_capacity_iff_global_payment
    {V : Type*} [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {lam t delta : ℝ} {n : ℕ}
    (hcap : AngleCap p lam)
    (hn : 1 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdeltaHalf : delta < (1 : ℝ) / 2)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (cycles :
      letI : LinearOrder (ProjectionOrdered V) :=
        projectionLinearOrder hp
      ∀ i : ProjectionOrdered V,
        CentreProjectiveCycle (reindexedPoint_injective hp) i) :
    letI : LinearOrder (ProjectionOrdered V) :=
      projectionLinearOrder hp
    let htpos : 0 < t := by
      rw [ht]
      have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    let hwidth : t < (n : ℝ) + 1 := by rw [ht]; linarith
    let D := genericDirectionData_sendov hp hcap htpos hlam
    let B := standardResidualColoring D n (by exact_mod_cast hwidth)
    let k : ProjectionOrdered V → ℕ :=
      fun i => centreExponent (cycles i) t
    ((∑ i : ProjectionOrdered V, 2 ^ k i) ≤ 2 ^ n) ↔
      ((overlapCompletionWords B).card +
          totalDyadicProfileLoss k (projectedFree B) ≤
        (2 ^ n - (coveredCompletionWords B).card) +
          totalDyadicProfileSurplus k (projectedFree B)) := by
  classical
  letI : LinearOrder (ProjectionOrdered V) := projectionLinearOrder hp
  have htpos : 0 < t := by
    rw [ht]
    have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hwidth : t < (n : ℝ) + 1 := by
    rw [ht]
    linarith
  let D := genericDirectionData_sendov hp hcap htpos hlam
  let B : OrderedEdgeColoring (ProjectionOrdered V) (n + 1) :=
    standardResidualColoring D n (by exact_mod_cast hwidth)
  let k : ProjectionOrdered V → ℕ :=
    fun i => centreExponent (cycles i) t
  change
    ((∑ i : ProjectionOrdered V, 2 ^ k i) ≤ 2 ^ n) ↔
      ((overlapCompletionWords B).card +
          totalDyadicProfileLoss k (projectedFree B) ≤
        (2 ^ n - (coveredCompletionWords B).card) +
          totalDyadicProfileSurplus k (projectedFree B))
  exact residual_projection_accounting_iff
    k (projectedFree B) n
    (coveredCompletionWords B).card
    (overlapCompletionWords B).card
    (coveredCompletionWords_card_le_two_pow B)
    (projectedFree_mass_eq_covered_add_overlap B)

#print axioms planar_lower_branch_dyadic_capacity_of_global_payment
#print axioms planar_lower_branch_dyadic_capacity_iff_global_payment

end ProjectionOrdered
end JSP000404Research
