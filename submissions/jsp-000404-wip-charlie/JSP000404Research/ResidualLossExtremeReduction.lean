import JSP000404Research.ResidualLossDirectedFibre
import Mathlib.Data.Finset.Order
import Mathlib.Tactic

/-!
# Extreme-loss reduction for globally directed translations

On a finite nonempty linear order, let top and bottom be the maximum and minimum
vertices.

If top is not a projected-loss vertex, every projected-loss vertex lies
strictly below top, so all loss vertices admit a common outgoing-coordinate
choice.  Dually, if bottom is not a loss vertex, all loss vertices admit a
common incoming-coordinate choice.

Therefore the genuinely two-sided translated-loss fibre phenomenon can only
survive when both global extremes are themselves projected-loss vertices.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem exists_global_outgoing_loss_choice_of_top_not_loss
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V] {n : ℕ}
    (hn : 0 < n)
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hTopNotLoss :
      (Finset.univ.max' (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty))
        ∉ projectedLossVertices C exponent) :
    ∃ choice : V → Fin n,
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        choice v ∈ outgoingRetained C v ∧
        choice v ∈ retainedActive C v := by
  classical
  let top : V :=
    Finset.univ.max'
      (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
  have htop :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        v < top := by
    intro v hv
    have hvle : v ≤ top := by
      exact Finset.le_max' Finset.univ v (Finset.mem_univ v)
    have hvne : v ≠ top := by
      intro h
      subst v
      exact hTopNotLoss hv
    exact lt_of_le_of_ne hvle hvne
  exact exists_outgoing_loss_choice_of_common_top
    hn C exponent hexp honeLoss top htop

theorem exists_global_incoming_loss_choice_of_bottom_not_loss
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V] {n : ℕ}
    (hn : 0 < n)
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hBottomNotLoss :
      (Finset.univ.min' (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty))
        ∉ projectedLossVertices C exponent) :
    ∃ choice : V → Fin n,
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        choice v ∈ incomingRetained C v ∧
        choice v ∈ retainedActive C v := by
  classical
  let bottom : V :=
    Finset.univ.min'
      (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
  have hbottom :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        bottom < v := by
    intro v hv
    have hle : bottom ≤ v := by
      exact Finset.min'_le Finset.univ v (Finset.mem_univ v)
    have hne : bottom ≠ v := by
      intro h
      subst v
      exact hBottomNotLoss hv
    exact lt_of_le_of_ne hle hne
  exact exists_incoming_loss_choice_of_common_bottom
    hn C exponent hexp honeLoss bottom hbottom

theorem projectedLoss_extreme_case_split
    {V : Type*} [LinearOrder V] [Fintype V] [Nonempty V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    let top :=
      Finset.univ.max'
        (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
    let bottom :=
      Finset.univ.min'
        (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
    top ∉ projectedLossVertices C exponent
    ∨
    bottom ∉ projectedLossVertices C exponent
    ∨
    (top ∈ projectedLossVertices C exponent ∧
      bottom ∈ projectedLossVertices C exponent) := by
  classical
  dsimp
  by_cases ht :
      Finset.univ.max'
        (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
        ∈ projectedLossVertices C exponent
  · by_cases hb :
      Finset.univ.min'
        (Finset.univ_nonempty : (Finset.univ : Finset V).Nonempty)
        ∈ projectedLossVertices C exponent
    · exact Or.inr (Or.inr ⟨ht,hb⟩)
    · exact Or.inr (Or.inl hb)
  · exact Or.inl ht

#print axioms exists_global_outgoing_loss_choice_of_top_not_loss
#print axioms exists_global_incoming_loss_choice_of_bottom_not_loss
#print axioms projectedLoss_extreme_case_split

end OrderedEdgeColoring
end JSP000404Research
