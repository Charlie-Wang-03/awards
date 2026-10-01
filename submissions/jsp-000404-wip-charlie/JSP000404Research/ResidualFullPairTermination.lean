import JSP000404Research.ResidualFullPairProgress
import Mathlib.Tactic

/-!
# Finite length of strict full-pair dimension growth

ResidualFullPairProgress proves that every non-rematching full transition
strictly increases the common-inactive dimension, and that this dimension is
bounded by n.

This file isolates the finite combinatorial consequence: any strictly
dimension-increasing chain has at most n transitions.

Equal-dimension full transitions are deliberately excluded here because they
are explicit bijective rematchings of overlap cubes and should be contracted
by the global Hall argument rather than treated as progress steps.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem strict_dimension_chain_length_le
    {m n : ℕ}
    (dim : Fin (m + 1) → ℕ)
    (hbound : ∀ i, dim i ≤ n)
    (hstrict : StrictMono dim) :
    m ≤ n := by
  let f : Fin (m + 1) → Fin (n + 1) :=
    fun i => ⟨dim i, by
      have hi := hbound i
      omega⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hstrict.injective
    exact congrArg Fin.val hij
  have hcard :=
    Fintype.card_le_of_injective f hfinj
  simpa using hcard

theorem commonInactive_strict_chain_length_le
    {V : Type*} [LinearOrder V]
    {n m : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (left right : Fin (m + 1) → V)
    (hstrict :
      StrictMono
        (fun i =>
          (commonInactiveRetained C (left i) (right i)).card)) :
    m ≤ n := by
  apply strict_dimension_chain_length_le
    (fun i =>
      (commonInactiveRetained C (left i) (right i)).card)
  · intro i
    exact commonInactive_card_le_n C (left i) (right i)
  · exact hstrict

#print axioms strict_dimension_chain_length_le
#print axioms commonInactive_strict_chain_length_le

end OrderedEdgeColoring
end JSP000404Research
