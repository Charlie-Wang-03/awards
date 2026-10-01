import JSP000404Research.ResidualEnlargedCollisionSimpleGraph
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

end OrderedEdgeColoring
end JSP000404Research
