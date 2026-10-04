import JSP000404Research.ResidualProjectionLoss
import JSP000404Research.WeightedOneLayerCharge
import JSP000404Research.ResidualVerticalPairs
import Mathlib.Tactic

/-!
# Lightweight projected-loss core

This module isolates the exact profile-loss vertex set and the two residual
incidence facts needed by local directional arguments.  It deliberately avoids
the retained-completion overlap / Boolean-hole machinery in ResidualLossWords.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def projectedLossVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset V :=
  oneLayerLossVertices exponent (projectedFree C)

@[simp] theorem mem_projectedLossVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (v : V) :
    v ∈ projectedLossVertices C exponent ↔
      exponent v = projectedFree C v + 1 := by
  simp [projectedLossVertices]

/-- A residual increasing edge makes the residual coordinate active at both
endpoints. -/
theorem residualCoord_mem_active_of_isResidual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v) :
    residualCoord n ∈ active C u ∧
      residualCoord n ∈ active C v := by
  classical
  have hval :
      (C.color u v).val = n :=
    residual_val_eq C hres
  have hcol :
      C.color u v = residualCoord n := by
    apply Fin.ext
    simpa [residualCoord] using hval
  constructor
  · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨v, huv, hcol⟩
  · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨u, huv, hcol⟩

theorem residual_inactive_of_mem_projectedLossVertices
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hv : v ∈ projectedLossVertices C exponent) :
    residualCoord n ∉ active C v := by
  have hexact :
      exponent v = projectedFree C v + 1 :=
    (mem_projectedLossVertices C exponent v).1 hv
  exact (exact_projected_loss_rigidity
    C exponent hexp honeLoss
    hexact rfl).1

#print axioms residualCoord_mem_active_of_isResidual
#print axioms residual_inactive_of_mem_projectedLossVertices

end OrderedEdgeColoring
end JSP000404Research
