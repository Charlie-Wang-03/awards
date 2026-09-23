
import JSP000404Research.ResidualSliceSeparation
import JSP000404Research.ResidualBudget
import Mathlib.Tactic

/-!
# Exact projected budget on residual-active vertices

Under the standard one-layer active-colour estimate

  card(active(v)) <= n - exponent(v) + 1,

a residual-active vertex loses the residual coordinate when projecting to the
first n retained colours.  Hence

  card(retainedActive(v)) <= n - exponent(v),

or equivalently

  exponent(v) <= projectedFree(v).

The hard residual-recolouring case is the exact equality case.  This file
packages the equivalent formulations so later geometry can focus only on
vertices which are simultaneously

* residual-active;
* retained-budget saturated;
* exact in the projected free profile;
* neither a profile-loss nor a profile-surplus vertex.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def ExactProjectedBudget
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (v : V) : Prop :=
  exponent v = projectedFree C v

theorem exactProjectedBudget_iff_retainedActive_card
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hexp : exponent v ≤ n) :
    ExactProjectedBudget C exponent v ↔
      (retainedActive C v).card = n - exponent v := by
  unfold ExactProjectedBudget projectedFree
  constructor <;> intro h
  · omega
  · omega

theorem exactProjectedBudget_iff_not_loss_not_surplus
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V} :
    ExactProjectedBudget C exponent v ↔
      dyadicProfileLoss exponent (projectedFree C) v = 0 ∧
      dyadicProfileSurplus exponent (projectedFree C) v = 0 := by
  unfold ExactProjectedBudget dyadicProfileLoss dyadicProfileSurplus
  constructor
  · intro h
    rw [h]
    simp
  · rintro ⟨hloss, hsur⟩
    by_cases hle : exponent v ≤ projectedFree C v
    · have hsurZero :
          2 ^ projectedFree C v - 2 ^ exponent v = 0 := hsur
      have hp :
          2 ^ exponent v ≤ 2 ^ projectedFree C v :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hle
      have heqPow : 2 ^ exponent v = 2 ^ projectedFree C v := by
        omega
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) heqPow
    · have hgt : projectedFree C v < exponent v := by omega
      have hp :
          2 ^ projectedFree C v < 2 ^ exponent v :=
        Nat.pow_lt_pow_right (by norm_num : 1 < 2) hgt
      have : 0 < 2 ^ exponent v - 2 ^ projectedFree C v := by
        omega
      omega

/-- Residual-active saturation is exactly projected-budget equality. -/
theorem exactProjectedBudget_of_residual_active_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    {v : V}
    (hres : residualCoord n ∈ active C v)
    (hsat :
      (retainedActive C v).card = n - exponent v) :
    ExactProjectedBudget C exponent v := by
  apply (exactProjectedBudget_iff_retainedActive_card
    C exponent (hexp v)).2
  exact hsat

/-- Conversely, exact projected budget gives retained saturation. -/
theorem retained_saturated_of_exactProjectedBudget
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    {v : V}
    (hexact : ExactProjectedBudget C exponent v) :
    (retainedActive C v).card = n - exponent v := by
  exact (exactProjectedBudget_iff_retainedActive_card
    C exponent (hexp v)).1 hexact

/-- Under the one-layer active estimate, every residual-active vertex is at
or below projected budget; equality is therefore the only hard local case. -/
theorem residual_active_projected_budget_dichotomy
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {v : V}
    (hres : residualCoord n ∈ active C v) :
    ExactProjectedBudget C exponent v ∨
      exponent v + 1 ≤ projectedFree C v := by
  have hle :=
    exponent_le_projectedFree_of_residual_mem
      C exponent hexp honeLoss hres
  by_cases heq : exponent v = projectedFree C v
  · exact Or.inl heq
  · right
    omega

#print axioms exactProjectedBudget_iff_retainedActive_card
#print axioms exactProjectedBudget_iff_not_loss_not_surplus
#print axioms residual_active_projected_budget_dichotomy

end OrderedEdgeColoring
end JSP000404Research
