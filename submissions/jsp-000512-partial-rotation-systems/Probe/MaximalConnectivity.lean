import Probe.PendantInsertion

namespace JSP512Probe.EdgeInsertion
open RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V] (u v : V) (hne : u ≠ v)

/-- A graph consisting of a single edge has singleton rotations at both endpoints. -/
def singleEdgeRotation : RotationSystem (addedGraph (⊥ : SimpleGraph V) u v hne) where
  rotate := 1
  source _ := rfl
  local_cycle d e h := by
    suffices d = e by subst e; exact Equiv.Perm.SameCycle.rfl
    apply SimpleGraph.Dart.ext
    apply Prod.ext h
    rcases d.adj with hd | hd | hd
    · exact hd.elim
    · rcases e.adj with he | he | he
      · exact he.elim
      · exact hd.2.trans he.2.symm
      · exact False.elim (hne (hd.1.symm.trans (h.trans he.1)))
    · rcases e.adj with he | he | he
      · exact he.elim
      · exact False.elim (hne (he.1.symm.trans (h.symm.trans hd.1)))
      · exact hd.2.trans he.2.symm

theorem singleEdge_genusZero : (singleEdgeRotation u v hne).HasGenusZero := by
  classical
  let R := singleEdgeRotation u v hne
  let d : (addedGraph (⊥ : SimpleGraph V) u v hne).Dart :=
    embedDart ⊥ u v hne (some none)
  have hd : DeletedGraph d = ⊥ := by
    ext x y
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, SimpleGraph.bot_adj]
    change (((⊥ : SimpleGraph V).Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧
      s(x,y) ≠ s(u,v)) ↔ False
    simp only [SimpleGraph.bot_adj, false_or, ne_eq, Sym2.eq_iff]
    tauto
  have hb : (addedGraph (⊥ : SimpleGraph V) u v hne).IsBridge d.edge := by
    change ¬(DeletedGraph d).Reachable u v
    rw [hd, SimpleGraph.reachable_bot]
    exact hne
  have hz : (R.deleteEdge d).eulerDefect = 0 := by
    generalize R.deleteEdge d = S
    revert S
    rw [hd]
    exact bot_defect
  exact (R.bridge_defect d hb).trans hz

end JSP512Probe.EdgeInsertion

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Maximal genus-zero graphs are preconnected, also for empty vertex types. -/
theorem maximal_preconnected (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) : G.Preconnected := by
  classical
  by_cases hg : G = ⊥
  · subst G
    intro u v
    by_cases huv : u = v
    · exact huv ▸ SimpleGraph.Reachable.rfl
    · let H := EdgeInsertion.addedGraph (⊥ : SimpleGraph V) u v huv
      have hh := maximal_supergraph_eq hmax H bot_le
        ⟨_, EdgeInsertion.singleEdge_genusZero u v huv⟩
      have ha : H.Adj u v := Or.inr (Or.inl ⟨rfl,rfl⟩)
      rw [hh] at ha
      exact ha.elim
  · obtain ⟨u,v,h⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hg
    exact (R.maximal_connected_of_dart hz hmax ⟨(u,v),h⟩).preconnected

/-- Every maximal genus-zero graph on a nonempty vertex type is connected. -/
theorem maximal_connected [Nonempty V] (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) : G.Connected :=
  ⟨R.maximal_preconnected hz hmax⟩

end JSP512Probe.RotationSystem
