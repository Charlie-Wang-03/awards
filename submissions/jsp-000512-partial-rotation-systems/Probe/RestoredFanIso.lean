import Probe.FanStart

namespace JSP512Probe.RotationSystem
variable {V : Type*} (G : SimpleGraph V) (v : V) (A : Set {u : V | u ≠ v})
  (K : SimpleGraph (Option A))

/-- The temporary fresh-center graph is exactly the restored induced side
once its old edges and center neighbors match the original graph. -/
noncomputable def restoredFanIso
    (hold : ∀ x y : A, K.Adj (some x) (some y) ↔ G.Adj x.val.val y.val.val)
    (hcenter : ∀ x : A, K.Adj none (some x) ↔ G.Adj v x.val.val) :
    K ≃g G.induce (restoreSide v A) := by
  refine ⟨restoredVertexEquiv v A, ?_⟩
  intro x y
  cases x with
  | none =>
    cases y with
    | none => exact ⟨fun h => False.elim (G.irrefl h), fun h => False.elim (K.irrefl h)⟩
    | some y => exact (hcenter y).symm
  | some x =>
    cases y with
    | none =>
      change G.Adj x.val.val v ↔ K.Adj (some x) none
      rw [G.adj_comm, K.adj_comm]
      exact (hcenter x).symm
    | some y => exact (hold x y).symm

end JSP512Probe.RotationSystem
