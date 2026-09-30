import JSP000404Research.ResidualLossTranslatedBlock
import JSP000404Research.ResidualProjectionLoss
import Mathlib.Tactic

/-!
# Exact local candidate capacity at a projected-loss vertex

A projected-loss vertex satisfies

  exponent(v) = projectedFree(v) + 1.

Its retained completion cube therefore has only half of the target dyadic mass.
If c is any retained active coordinate, flipping c produces a translated cube
of the same size and disjoint from the original cube.

Hence the doubled local block

  Q_v union flip_c(Q_v)

has cardinality exactly

  2 ^ exponent(v).

This is the precise local candidate block needed by the weighted Hall
formulation. The remaining difficulty is purely global: expansion of unions of
these blocks across different vertices.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def doubledCompletionBlock
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (c : Fin n) :
    Finset (Fin n → Bool) :=
  retainedCompletionWords C v ∪
    translatedCompletionWords C v c

theorem doubledCompletionBlock_card_of_active
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c : Fin n}
    (hc : c ∈ retainedActive C v) :
    (doubledCompletionBlock C v c).card =
      2 * (retainedCompletionWords C v).card := by
  classical
  unfold doubledCompletionBlock
  rw [Finset.card_union_of_disjoint]
  · rw [translatedCompletionWords_card]
    omega
  · exact
      (translatedCompletionWords_disjoint_original_of_active
        C hc).symm

theorem projectedLoss_doubledBlock_card_eq_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {c : Fin n}
    (hc : c ∈ retainedActive C v) :
    (doubledCompletionBlock C v c).card =
      2 ^ exponent v := by
  have hlossEq :
      exponent v = projectedFree C v + 1 :=
    (mem_projectedLossVertices C exponent v).1 hvLoss
  rw [doubledCompletionBlock_card_of_active C hc,
      retainedCompletionWords_card]
  unfold projectedFree at hlossEq
  rw [hlossEq, pow_succ]
  ring

theorem nonloss_completionBlock_target_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {v : V}
    (hprofile : exponent v ≤ projectedFree C v) :
    2 ^ exponent v ≤
      (retainedCompletionWords C v).card := by
  rw [retainedCompletionWords_card]
  exact Nat.pow_le_pow_right
    (by norm_num : 0 < 2) hprofile

#print axioms doubledCompletionBlock_card_of_active
#print axioms projectedLoss_doubledBlock_card_eq_target
#print axioms nonloss_completionBlock_target_le

end OrderedEdgeColoring
end JSP000404Research
