import JSP000404Research.ResidualLossFibreRank
import Mathlib.Tactic

/-!
# Exponent–rank tradeoff inside translated loss fibres

Let F_y denote the vertices whose translated loss block contains a fixed
Boolean completion word y. When the chosen coordinates are retained-active,
the true-labelled prefix of F_y up to w injects into retainedActive(w).
For a projected-loss vertex this palette has exact size n+1-exponent(w).
The analogous statement holds for the false-labelled suffix.

These are local, unconditional consequences of the established one-layer loss
rigidity and fibre colour classification. No Hall injection is postulated.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translatedLossFibre_true_prefix_exponent_budget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ v,
        v ∈ translatedLossFibre C exponent choice word →
        choice v ∈ retainedActive C v)
    {w : V}
    (hw : w ∈ translatedLossFibre C exponent choice word)
    (hwTrue : word (choice w) = true) :
    (translatedLossFibrePrefix C exponent choice word w).card +
      exponent w ≤ n + 1 := by
  have hwLoss : w ∈ projectedLossVertices C exponent :=
    ((mem_translatedLossFibre C exponent choice word w).1 hw).1
  have hsat :
      (retainedActive C w).card = n - exponent w + 1 :=
    (exact_projected_loss_rigidity
      C exponent hexp honeLoss
      ((mem_projectedLossVertices C exponent w).1 hwLoss)
      rfl).2
  have hprefix :=
    true_top_prefix_card_le_retainedActive
      C exponent hexp honeLoss choice word hactive hw hwTrue
  have hk := hexp w
  omega

theorem translatedLossFibre_false_suffix_exponent_budget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (word : Fin n → Bool)
    (hactive :
      ∀ v,
        v ∈ translatedLossFibre C exponent choice word →
        choice v ∈ retainedActive C v)
    {v : V}
    (hv : v ∈ translatedLossFibre C exponent choice word)
    (hvFalse : word (choice v) = false) :
    (translatedLossFibreSuffix C exponent choice word v).card +
      exponent v ≤ n + 1 := by
  have hvLoss : v ∈ projectedLossVertices C exponent :=
    ((mem_translatedLossFibre C exponent choice word v).1 hv).1
  have hsat :
      (retainedActive C v).card = n - exponent v + 1 :=
    (exact_projected_loss_rigidity
      C exponent hexp honeLoss
      ((mem_projectedLossVertices C exponent v).1 hvLoss)
      rfl).2
  have hsuffix :=
    false_bottom_suffix_card_le_retainedActive
      C exponent hexp honeLoss choice word hactive hv hvFalse
  have hk := hexp v
  omega

#print axioms translatedLossFibre_true_prefix_exponent_budget
#print axioms translatedLossFibre_false_suffix_exponent_budget

end OrderedEdgeColoring
end JSP000404Research
