import Probe.InducedDiskLists
import Probe.ChordDiskSeparator

namespace JSP512Probe.RotationSystem.ChordSectorData
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {R : RotationSystem G}
  {outer : G.Dart} {w : V}

/-- Restoring the deleted center does not introduce the old predecessor into
the exposed side. -/
theorem predecessor_not_restored_exposed (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b) : outer.fst ∉ restoreSide outer.snd D.exposedSide := by
  rintro (he | ⟨u,hu,he⟩)
  · exact outer.adj.ne he
  · exact D.exposed_avoids_predecessor hsimple ⟨u,hu⟩ he

/-- A protected edge incident to the predecessor is wholly in the first
restored side. Any protected vertex also on the second side is a chord endpoint.
This establishes vertex/list placement, not facial placement of the edge. -/
theorem protected_vertices (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (q : V) (hq : G.Adj outer.fst q) :
    outer.fst ∈ restoreSide outer.snd D.boundarySide ∧
    q ∈ restoreSide outer.snd D.boundarySide ∧
    ∀ u ∈ restoreSide outer.snd D.exposedSide,
      u = outer.fst ∨ u = q → u = outer.snd ∨ u = w := by
  have hsep := D.separator
  exact ListColoring.protected_edge_side G _ _ outer.snd w outer.fst q
    hsep.2.1 hsep.2.2.1 (D.predecessor_not_restored_exposed hsimple) hq

end JSP512Probe.RotationSystem.ChordSectorData
