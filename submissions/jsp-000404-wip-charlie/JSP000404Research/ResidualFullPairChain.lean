import JSP000404Research.ResidualFullPairTermination
import Mathlib.Tactic

/-!
# Finite-chain dichotomy for full-pair progress

Abstract the output of ResidualFullPairProgress along a finite sequence of
full-pair states.  At each transition the common-inactive dimension either

* stays equal, corresponding to an explicit rematching equivalence, or
* strictly increases.

Since every dimension lies in [0,n], a chain with more than n transitions must
contain an equal-dimension/rematching step. Equivalently, any segment with no
rematching has at most n transitions.

This is the finite termination statement required by the global Hall
contraction: equal-mass steps may be contracted as rematching equivalences;
all remaining full transitions form uniformly bounded acyclic segments.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem dimension_chain_equal_step_or_length_le
    {m n : ℕ}
    (dim : Fin (m + 1) → ℕ)
    (hbound : ∀ i, dim i ≤ n)
    (hstep :
      ∀ i : Fin m,
        dim i.castSucc = dim i.succ
        ∨ dim i.castSucc < dim i.succ) :
    (∃ i : Fin m,
      dim i.castSucc = dim i.succ)
    ∨
    m ≤ n := by
  by_cases heq :
      ∃ i : Fin m,
        dim i.castSucc = dim i.succ
  · exact Or.inl heq
  · right
    have hstrictSucc :
        ∀ i : Fin m,
          dim i.castSucc < dim i.succ := by
      intro i
      rcases hstep i with hEq | hLt
      · exact False.elim (heq ⟨i,hEq⟩)
      · exact hLt
    have hstrict : StrictMono dim := by
      exact strictMono_fin_of_lt_succ hstrictSucc
    exact strict_dimension_chain_length_le
      dim hbound hstrict

theorem commonInactive_chain_rematch_or_length_le
    {V : Type*} [LinearOrder V]
    {n m : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (left right : Fin (m + 1) → V)
    (hstep :
      ∀ i : Fin m,
        (commonInactiveRetained C
          (left i.castSucc) (right i.castSucc)).card
          =
        (commonInactiveRetained C
          (left i.succ) (right i.succ)).card
        ∨
        (commonInactiveRetained C
          (left i.castSucc) (right i.castSucc)).card
          <
        (commonInactiveRetained C
          (left i.succ) (right i.succ)).card) :
    (
      ∃ i : Fin m,
        (commonInactiveRetained C
          (left i.castSucc) (right i.castSucc)).card
          =
        (commonInactiveRetained C
          (left i.succ) (right i.succ)).card
    )
    ∨
    m ≤ n := by
  apply dimension_chain_equal_step_or_length_le
    (fun i =>
      (commonInactiveRetained C (left i) (right i)).card)
  · intro i
    exact commonInactive_card_le_n C (left i) (right i)
  · exact hstep

#print axioms dimension_chain_equal_step_or_length_le
#print axioms commonInactive_chain_rematch_or_length_le

end OrderedEdgeColoring
end JSP000404Research
