import JSP000404Research.ResidualProjectionLoss
import JSP000404Research.ResidualHoleInjection
import Mathlib.Tactic

/-!
# Residual-inactive vertices have unique retained codes

A residual increasing edge makes the residual colour active at both endpoints.
Therefore a vertex at which the residual colour is inactive cannot share its
retained Boolean code with any other vertex: equal retained codes would force
their connecting edge to be residual.

Combined with ResidualProjectionLoss, every exact one-layer tail-loss vertex
has a unique retained base code.

This is the Boolean-hole starting point for paying the remaining one-layer
profile losses.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem residualCoord_mem_active_of_isResidual
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V}
    (huv : u < v)
    (hres : IsResidual C u v) :
    residualCoord n ∈ active C u ∧
      residualCoord n ∈ active C v := by
  have hcol : C.color u v = residualCoord n := by
    apply Fin.ext
    simpa [residualCoord] using residual_val_eq C hres
  constructor
  · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨v, huv, hcol⟩
  · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨u, huv, hcol⟩

theorem sameRetained_eq_of_residual_inactive
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V}
    (hinactive : residualCoord n ∉ active C v)
    (hsame : SameRetained C v w) :
    v = w := by
  by_contra hvw
  rcases lt_or_gt_of_ne hvw with hvwlt | hwvlt
  · have hres :=
      isResidual_of_sameRetained_lt C hvwlt hsame
    exact hinactive
      (residualCoord_mem_active_of_isResidual C hvwlt hres).1
  · have hres :=
      isResidual_of_sameRetained_lt
        C hwvlt (sameRetained_symm hsame)
    exact hinactive
      (residualCoord_mem_active_of_isResidual C hwvlt hres).2

/-- Exact one-layer profile losses have unique retained Boolean codes. -/
theorem sameRetained_eq_of_exact_projected_loss
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {r : ℕ} {v w : V}
    (hv :
      v ∈ layerLossSet exponent (projectedFree C) r)
    (hsame : SameRetained C v w) :
    v = w := by
  have hinactive :=
    residual_inactive_of_mem_layerLoss_projected
      C exponent hexp honeLoss hv
  exact sameRetained_eq_of_residual_inactive
    C hinactive hsame

#print axioms residualCoord_mem_active_of_isResidual
#print axioms sameRetained_eq_of_residual_inactive
#print axioms sameRetained_eq_of_exact_projected_loss

end OrderedEdgeColoring
end JSP000404Research
