
import JSP000404Research.ResidualOverlapSurplus
import JSP000404Research.ResidualActiveDrop
import Mathlib.Tactic

/-!
# Saturated residual endpoints are exact one-layer budget failures

Dropping the last colour from an (n+1)-colour ordered colouring loses exactly
one active colour at a vertex whenever the residual colour is active there:

  card(active(v)) = card(retainedActive(v)) + 1.

Hence if the target exponent saturates the projected retained free count,

  exponent(v) = n - card(retainedActive(v)),

then

  card(active(v)) = n - exponent(v) + 1,

so the original exact n-colour budget is missed by exactly one.

This is the bridge from an unpaid projected-overlap carrier (which must have a
saturated endpoint) back to the one-exception phase-budget-failure geometry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- If the residual colour is active, dropping it decreases active-cardinality
by exactly one. -/
theorem active_card_eq_retainedActive_card_add_one_of_residual_mem
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V)
    (hres : residualCoord n ∈ active C v) :
    (active C v).card =
      (retainedActive C v).card + 1 := by
  classical
  let R : Finset (Fin (n + 1)) :=
    (retainedActive C v).map Fin.castSuccEmb
  have hRcard :
      R.card = (retainedActive C v).card := by
    simp [R]
  have hsub :
      active C v ⊆ insert (residualCoord n) R := by
    intro c hc
    by_cases hlt : c.val < n
    · let d : Fin n := ⟨c.val, hlt⟩
      have hdcast : d.castSucc = c := by
        apply Fin.ext
        rfl
      have hdActive :
          d ∈ retainedActive C v := by
        apply (castSucc_mem_active_iff_mem_retainedActive
          C v d).1
        simpa [hdcast] using hc
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_map.mpr
      exact ⟨d, hdActive, hdcast⟩
    · have hcval : c.val = n := by
        have hcLt := c.isLt
        omega
      have hcres : c = residualCoord n := by
        apply Fin.ext
        simpa [residualCoord] using hcval
      exact Finset.mem_insert.mpr (Or.inl hcres)
  have hupper :
      (active C v).card ≤
        (retainedActive C v).card + 1 := by
    have hcard :=
      Finset.card_le_card hsub
    have hins :
        (insert (residualCoord n) R).card ≤ R.card + 1 :=
      Finset.card_insert_le _ _
    omega
  have hlower :=
    retainedActive_card_add_one_le_active_of_residual_mem
      C v hres
  omega

/-- Saturation of the projected free profile makes the one-layer active bound
an equality. -/
theorem active_card_eq_exact_one_loss_of_residual_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hsat : exponent v = projectedFree C v)
    (hres : residualCoord n ∈ active C v) :
    (active C v).card = n - exponent v + 1 := by
  have hactive :=
    active_card_eq_retainedActive_card_add_one_of_residual_mem
      C v hres
  have hretN :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  unfold projectedFree at hsat
  omega

/-- The same endpoint strictly fails the exact n-colour budget by one. -/
theorem exact_budget_fails_of_residual_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hsat : exponent v = projectedFree C v)
    (hres : residualCoord n ∈ active C v) :
    n - exponent v < (active C v).card := by
  rw [active_card_eq_exact_one_loss_of_residual_saturated
      C exponent hsat hres]
  omega

/-- Conversely, under the global one-layer bound and residual activity, strict
failure of the exact budget forces projected saturation. -/
theorem residual_bad_implies_projected_saturated
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hexp : exponent v ≤ n)
    (honeLoss :
      (active C v).card ≤ n - exponent v + 1)
    (hres : residualCoord n ∈ active C v)
    (hbad : n - exponent v < (active C v).card) :
    exponent v = projectedFree C v := by
  have hactive :=
    active_card_eq_retainedActive_card_add_one_of_residual_mem
      C v hres
  have hretN :
      (retainedActive C v).card ≤ n := by
    simpa using Finset.card_le_univ (retainedActive C v)
  unfold projectedFree
  omega

#print axioms active_card_eq_retainedActive_card_add_one_of_residual_mem
#print axioms active_card_eq_exact_one_loss_of_residual_saturated
#print axioms exact_budget_fails_of_residual_saturated

end OrderedEdgeColoring
end JSP000404Research
