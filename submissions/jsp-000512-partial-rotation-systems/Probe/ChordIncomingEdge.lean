import Probe.ChordSides
import Probe.SideBoundaryInheritance

namespace JSP512Probe.RotationSystem.ChordSectorData
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {R : RotationSystem G}
  {outer : G.Dart} {w : V}

/-- Every surviving dart entering the old predecessor belongs to the
old-boundary component, including when its source is the shared chord vertex. -/
theorem incoming_component (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (z : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (ht : z.snd.val = outer.fst) :
    let S := R.deleteVertex outer.snd
    let hxy := D.cut_source.trans (congrArg (fun z => z.fst) D.sector_cut)
    (RefinedRotation.graph _ (S.splitRotation D.x (D.firstPath 0))
      (S.split_source D.x (D.firstPath 0) hxy)).Reachable
      (RefinedRotation.vertex _ (S.splitRotation D.x (D.firstPath 0)) z)
      (RefinedRotation.vertex _ (S.splitRotation D.x (D.firstPath 0)) D.x) := by
  let S := R.deleteVertex outer.snd
  have hxy := D.cut_source.trans (congrArg (fun z => z.fst) D.sector_cut)
  have hne : D.x ≠ D.firstPath 0 := by
    simpa only [D.sector_cut, firstPath] using D.cut_ne
  obtain ⟨u,hu,hm,_⟩ := D.predecessor_side hsimple
  have hmem : z.symm.fst ∈ D.boundarySide := by
    have he : z.symm.fst = u := Subtype.ext (ht.trans hu.symm)
    exact he ▸ hm
  have haway : z.symm.fst ≠ D.x.fst := by
    intro he
    exact D.chord_ne_predecessor
      (D.chord_vertex.symm.trans ((congrArg Subtype.val he).symm.trans ht))
  have hr := S.splitSide_source_membership D.x (D.firstPath 0) hxy hne D.x z.symm haway hmem
  apply SimpleGraph.Reachable.trans _ hr
  exact SimpleGraph.Adj.reachable ⟨z,rfl,rfl⟩

end JSP512Probe.RotationSystem.ChordSectorData
