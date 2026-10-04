import JSP000404Research.ResidualProjectedLossCore
import JSP000404Research.RetainedOrientation
import Mathlib.Tactic

/-!
# Directional retained witnesses at projected-loss vertices

A projected-loss vertex is residual-inactive. Therefore every incident edge is
retained: a residual incident edge would activate the residual coordinate at
that endpoint.

Consequently:

* every later vertex supplies an outgoing retained coordinate;
* every earlier vertex supplies an incoming retained coordinate.

Hence every non-maximum projected-loss vertex has an outgoing translation
direction, and every non-minimum projected-loss vertex has an incoming
translation direction. Combined with triangular blocker support, this permits
directional displacement toward either side except at the corresponding
extreme endpoint.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem projectedLoss_edge_right_retained
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v < w) :
    (C.color v w).val < n := by
  by_contra hnot
  have hres : IsResidual C v w := hnot
  have hactive :=
    (residualCoord_mem_active_of_isResidual C hvw hres).1
  exact
    (residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hvLoss) hactive

theorem projectedLoss_edge_left_retained
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {u v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huv : u < v) :
    (C.color u v).val < n := by
  by_contra hnot
  have hres : IsResidual C u v := hnot
  have hactive :=
    (residualCoord_mem_active_of_isResidual C huv hres).2
  exact
    (residual_inactive_of_mem_projectedLossVertices
      C exponent hexp honeLoss hvLoss) hactive

theorem projectedLoss_outgoing_witness_of_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hvw : v < w) :
    ∃ c : Fin n,
      c ∈ outgoingRetained C v ∧
      c ∈ retainedActive C v := by
  let hret :=
    projectedLoss_edge_right_retained
      C exponent hexp honeLoss hvLoss hvw
  let c : Fin n := retainedColor C v w hret
  refine ⟨c,?_,?_⟩
  · apply (mem_outgoingRetained_iff C v c).2
    refine ⟨w,hvw,?_⟩
    apply Fin.ext
    rfl
  · rw [retainedActive_eq_incoming_union_outgoing C v]
    apply Finset.mem_union_right
    apply (mem_outgoingRetained_iff C v c).2
    refine ⟨w,hvw,?_⟩
    apply Fin.ext
    rfl

theorem projectedLoss_incoming_witness_of_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {u v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (huv : u < v) :
    ∃ c : Fin n,
      c ∈ incomingRetained C v ∧
      c ∈ retainedActive C v := by
  let hret :=
    projectedLoss_edge_left_retained
      C exponent hexp honeLoss hvLoss huv
  let c : Fin n := retainedColor C u v hret
  refine ⟨c,?_,?_⟩
  · apply (mem_incomingRetained_iff C v c).2
    refine ⟨u,huv,?_⟩
    apply Fin.ext
    rfl
  · rw [retainedActive_eq_incoming_union_outgoing C v]
    apply Finset.mem_union_left
    apply (mem_incomingRetained_iff C v c).2
    refine ⟨u,huv,?_⟩
    apply Fin.ext
    rfl

theorem projectedLoss_has_outgoing_of_exists_greater
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hgt : ∃ w : V, v < w) :
    (outgoingRetained C v).Nonempty := by
  obtain ⟨w,hvw⟩ := hgt
  obtain ⟨c,hcOut,_hcActive⟩ :=
    projectedLoss_outgoing_witness_of_lt
      C exponent hexp honeLoss hvLoss hvw
  exact ⟨c,hcOut⟩

theorem projectedLoss_has_incoming_of_exists_less
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    (hlt : ∃ u : V, u < v) :
    (incomingRetained C v).Nonempty := by
  obtain ⟨u,huv⟩ := hlt
  obtain ⟨c,hcIn,_hcActive⟩ :=
    projectedLoss_incoming_witness_of_lt
      C exponent hexp honeLoss hvLoss huv
  exact ⟨c,hcIn⟩

#print axioms projectedLoss_edge_right_retained
#print axioms projectedLoss_edge_left_retained
#print axioms projectedLoss_has_outgoing_of_exists_greater
#print axioms projectedLoss_has_incoming_of_exists_less

end OrderedEdgeColoring
end JSP000404Research
