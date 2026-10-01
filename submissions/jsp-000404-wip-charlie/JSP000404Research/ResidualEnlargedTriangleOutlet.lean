import JSP000404Research.ResidualEnlargedCollisionSimpleGraph
import JSP000404Research.ResidualExactSharedRecursiveOutlet
import Mathlib.Tactic

/-!
# Structured outlet for collision triangles

A raw triangle in the enlarged collision graph is too weak as a recursive
obstruction: it does not record where projected loss occurs.

The existing triangle-loss classification gives exactly two meaningful
possibilities.

* At least two triangle vertices are projected-loss.
* Exactly one vertex is projected-loss; then the edge joining the two
  non-loss vertices is necessarily a residual edge.

This file packages that dichotomy as a small inductive outlet suitable for the
planar root reduction.  No geometric information is discarded.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

inductive EnlargedTriangleOutlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (T : Finset V)
    (u v w : {x : V // x ∈ T}) : Prop
  | twoLossUV
      (huLoss : u.1 ∈ projectedLossVertices C exponent)
      (hvLoss : v.1 ∈ projectedLossVertices C exponent)
  | twoLossUW
      (huLoss : u.1 ∈ projectedLossVertices C exponent)
      (hwLoss : w.1 ∈ projectedLossVertices C exponent)
  | twoLossVW
      (hvLoss : v.1 ∈ projectedLossVertices C exponent)
      (hwLoss : w.1 ∈ projectedLossVertices C exponent)
  | oneLossUResidual
      (huLoss : u.1 ∈ projectedLossVertices C exponent)
      (hvNonloss : v.1 ∉ projectedLossVertices C exponent)
      (hwNonloss : w.1 ∉ projectedLossVertices C exponent)
      (hres :
        (v.1 < w.1 ∧ IsResidual C v.1 w.1)
        ∨
        (w.1 < v.1 ∧ IsResidual C w.1 v.1))
  | oneLossVResidual
      (hvLoss : v.1 ∈ projectedLossVertices C exponent)
      (huNonloss : u.1 ∉ projectedLossVertices C exponent)
      (hwNonloss : w.1 ∉ projectedLossVertices C exponent)
      (hres :
        (u.1 < w.1 ∧ IsResidual C u.1 w.1)
        ∨
        (w.1 < u.1 ∧ IsResidual C w.1 u.1))
  | oneLossWResidual
      (hwLoss : w.1 ∈ projectedLossVertices C exponent)
      (huNonloss : u.1 ∉ projectedLossVertices C exponent)
      (hvNonloss : v.1 ∉ projectedLossVertices C exponent)
      (hres :
        (u.1 < v.1 ∧ IsResidual C u.1 v.1)
        ∨
        (v.1 < u.1 ∧ IsResidual C v.1 u.1))

theorem enlargedCollisionGraph_triangle_outlet
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (T : Finset V)
    {u v w : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (huw :
      (enlargedCollisionGraph C exponent T).Adj u w)
    (hvw :
      (enlargedCollisionGraph C exponent T).Adj v w) :
    EnlargedTriangleOutlet C exponent T u v w := by
  rcases
    enlargedCollisionGraph_triangle_loss_shape
      C exponent T huv huw hvw
    with hU | hV | hW | hUV | hUW | hVW
  · exact EnlargedTriangleOutlet.oneLossUResidual
      hU.huLoss hU.hvNonloss hU.hwNonloss
      (enlargedTriangle_oneLoss_has_nonloss_residual_edge
        C exponent hexp honeLoss T
        huv huw hvw
        hU.huLoss hU.hvNonloss hU.hwNonloss)
  · exact EnlargedTriangleOutlet.oneLossVResidual
      hV.hvLoss hV.huNonloss hV.hwNonloss
      (enlargedTriangle_oneLoss_has_nonloss_residual_edge
        C exponent hexp honeLoss T
        huv.symm hvw huw
        hV.hvLoss hV.huNonloss hV.hwNonloss)
  · exact EnlargedTriangleOutlet.oneLossWResidual
      hW.hwLoss hW.huNonloss hW.hvNonloss
      (enlargedTriangle_oneLoss_has_nonloss_residual_edge
        C exponent hexp honeLoss T
        huw.symm hvw.symm huv
        hW.hwLoss hW.huNonloss hW.hvNonloss)
  · exact EnlargedTriangleOutlet.twoLossUV
      hUV.huLoss hUV.hvLoss
  · exact EnlargedTriangleOutlet.twoLossUW
      hUW.huLoss hUW.hwLoss
  · exact EnlargedTriangleOutlet.twoLossVW
      hVW.hvLoss hVW.hwLoss

#print axioms enlargedCollisionGraph_triangle_outlet


/-- A collision edge between two non-loss vertices is already closed by the
profile trichotomy: a strict endpoint pays positive surplus, while an
exact--exact pair enters the existing exact recursive outlet. -/
theorem enlargedTriangle_nonloss_edge_paid_or_exactRecursive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (T : Finset V)
    {u v : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (huNonloss : u.1 ∉ projectedLossVertices C exponent)
    (hvNonloss : v.1 ∉ projectedLossVertices C exponent) :
    (
      ∃ w : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) w
    )
    ∨
    (
      ∃ source : V,
        ExactRecursiveOutlet C exponent source
    ) := by
  have hcross :=
    enlargedCollisionGraph_cross_of_adj
      C exponent T huv
  obtain ⟨word,huBlock,hvBlock⟩ := hcross
  have huWord :
      word ∈ retainedCompletionWords C u.1 := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent huNonloss] at huBlock
    exact huBlock
  have hvWord :
      word ∈ retainedCompletionWords C v.1 := by
    rw [enlargedProjectedCandidateBlock_nonloss
      C exponent hvNonloss] at hvBlock
    exact hvBlock
  have huvNe : u.1 ≠ v.1 := by
    intro h
    apply (enlargedCollisionGraph C exponent T).ne_of_adj huv
    apply Subtype.ext
    exact h
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss u.1
    with huStrict | huExact | huLoss
  · exact Or.inl
      ⟨u.1,
        projected_strict_surplus_at_least_one
          exponent (projectedFree C) huStrict⟩
  · rcases projectedProfile_strict_exact_or_loss
        C exponent hexp honeLoss v.1
      with hvStrict | hvExact | hvLoss
    · exact Or.inl
        ⟨v.1,
          projected_strict_surplus_at_least_one
            exponent (projectedFree C) hvStrict⟩
    · have hout :
          ExactSharedOutlet C exponent u.1 :=
        ExactSharedOutlet.exactPair
          v.1 huvNe hvExact word huWord hvWord
      exact Or.inr
        ⟨u.1,
          exactSharedOutlet_to_recursive
            C exponent huExact hout⟩
    · exact False.elim (hvNonloss hvLoss)
  · exact False.elim (huNonloss huLoss)

/-- Every enlarged collision triangle is therefore either already paid /
recursive, or its genuinely hard remainder contains two projected-loss
vertices. -/
theorem enlargedCollisionGraph_triangle_twoLoss_or_paid_or_exactRecursive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    (T : Finset V)
    {u v w : {x : V // x ∈ T}}
    (huv :
      (enlargedCollisionGraph C exponent T).Adj u v)
    (huw :
      (enlargedCollisionGraph C exponent T).Adj u w)
    (hvw :
      (enlargedCollisionGraph C exponent T).Adj v w) :
    (
      ∃ a b : {x : V // x ∈ T},
        a ≠ b ∧
        a.1 ∈ projectedLossVertices C exponent ∧
        b.1 ∈ projectedLossVertices C exponent
    )
    ∨
    (
      ∃ z : V,
        1 ≤ dyadicProfileSurplus
          exponent (projectedFree C) z
    )
    ∨
    (
      ∃ source : V,
        ExactRecursiveOutlet C exponent source
    ) := by
  rcases
    enlargedCollisionGraph_triangle_loss_shape
      C exponent T huv huw hvw
    with hU | hV | hW | hUV | hUW | hVW
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        hvw hU.hvNonloss hU.hwNonloss
      with hpaid | hrec
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr hrec)
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        huw hV.huNonloss hV.hwNonloss
      with hpaid | hrec
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr hrec)
  · rcases
      enlargedTriangle_nonloss_edge_paid_or_exactRecursive
        C exponent hexp honeLoss T
        huv hW.huNonloss hW.hvNonloss
      with hpaid | hrec
    · exact Or.inr (Or.inl hpaid)
    · exact Or.inr (Or.inr hrec)
  · exact Or.inl
      ⟨u,v,
        (enlargedCollisionGraph C exponent T).ne_of_adj huv,
        hUV.huLoss,hUV.hvLoss⟩
  · exact Or.inl
      ⟨u,w,
        (enlargedCollisionGraph C exponent T).ne_of_adj huw,
        hUW.huLoss,hUW.hwLoss⟩
  · exact Or.inl
      ⟨v,w,
        (enlargedCollisionGraph C exponent T).ne_of_adj hvw,
        hVW.hvLoss,hVW.hwLoss⟩

#print axioms enlargedTriangle_nonloss_edge_paid_or_exactRecursive
#print axioms enlargedCollisionGraph_triangle_twoLoss_or_paid_or_exactRecursive

end OrderedEdgeColoring
end JSP000404Research
