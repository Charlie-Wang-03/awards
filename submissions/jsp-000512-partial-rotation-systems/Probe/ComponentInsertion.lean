import Probe.MaximalBridges

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (a b : G.Dart)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Removing the new edge recovers exactly the original graph. -/
theorem delete_added_edge (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst) :
    (addedGraph G a.fst b.fst hne).deleteEdges {s(a.fst,b.fst)} = G := by
  ext x y
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  change ((G.Adj x y ∨ (x = a.fst ∧ y = b.fst) ∨ (x = b.fst ∧ y = a.fst)) ∧
    s(x,y) ≠ s(a.fst,b.fst)) ↔ G.Adj x y
  simp only [ne_eq, Sym2.eq_iff]
  constructor
  · tauto
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact hm h
    · exact hm h.symm

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem separate_component_count (hne : a.fst ≠ b.fst)
    (hn : ¬G.Reachable a.fst b.fst) :
    Nat.card G.ConnectedComponent =
      Nat.card (addedGraph G a.fst b.fst hne).ConnectedComponent + 1 := by
  classical
  have hm : ¬G.Adj a.fst b.fst := fun h => hn h.reachable
  let d : (addedGraph G a.fst b.fst hne).Dart := embedDart G a.fst b.fst hne (some none)
  have hd : DeletedGraph d = G := delete_added_edge G a b hne hm
  have hb : (addedGraph G a.fst b.fst hne).IsBridge d.edge := by
    change ¬(DeletedGraph d).Reachable a.fst b.fst
    rwa [hd]
  have hc := bridge_component_count d hb
  rwa [hd] at hc

theorem separate_face_count (hne : a.fst ≠ b.fst)
    (hn : ¬G.Reachable a.fst b.fst) :
    R.faceCount = (addEdge G R a b hne (fun h => hn h.reachable)).faceCount + 1 := by
  rw [added_face_count_eq_cut]
  apply swap_cycle_count
  intro hf
  have hr := face_reachable G R (R.rotate a) (R.rotate b) hf
  rw [R.source, R.source] at hr
  exact hn hr

/-- Joining two components at nonisolated vertices preserves Euler defect. -/
theorem separate_defect (hne : a.fst ≠ b.fst)
    (hn : ¬G.Reachable a.fst b.fst) :
    (addEdge G R a b hne (fun h => hn h.reachable)).eulerDefect = R.eulerDefect := by
  have hc := separate_component_count G a b hne hn
  have he := added_edge_count G a b hne (fun h => hn h.reachable)
  have hs := added_support G a b hne
  have hf := separate_face_count G R a b hne hn
  unfold eulerDefect supportSize
  rw [hs]
  omega

theorem separate_genusZero (hne : a.fst ≠ b.fst)
    (hn : ¬G.Reachable a.fst b.fst) (hz : R.HasGenusZero) :
    (addEdge G R a b hne (fun h => hn h.reachable)).HasGenusZero := by
  unfold HasGenusZero at hz ⊢
  rw [separate_defect G R a b hne hn, hz]

end JSP512Probe.EdgeInsertion

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (R : RotationSystem G)

/-- All nonisolated vertices of a maximal genus-zero graph lie in one component. -/
theorem maximal_dart_sources_reachable (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (a b : G.Dart) : G.Reachable a.fst b.fst := by
  classical
  by_contra hn
  have hne : a.fst ≠ b.fst := fun h => hn (h ▸ SimpleGraph.Reachable.rfl)
  let H := EdgeInsertion.addedGraph G a.fst b.fst hne
  have hz' := EdgeInsertion.separate_genusZero G R a b hne hn hz
  have hc := hmax H (fun _ _ h => Or.inl h) ⟨_, hz'⟩
  have he := EdgeInsertion.added_edge_count G a b hne (fun h => hn h.reachable)
  change Nat.card H.edgeSet = Nat.card G.edgeSet + 1 at he
  omega

/-- The support of a maximal genus-zero graph is contained in one component. -/
theorem maximal_support_reachable (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) {u v : V}
    (hu : u ∈ G.support) (hv : v ∈ G.support) : G.Reachable u v := by
  obtain ⟨x, hx⟩ := G.mem_support.mp hu
  obtain ⟨y, hy⟩ := G.mem_support.mp hv
  exact R.maximal_dart_sources_reachable hz hmax ⟨(u,x),hx⟩ ⟨(v,y),hy⟩

end JSP512Probe.RotationSystem
