import Probe.SplitSideChosenOuter
import Probe.ResidualFanVertices

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Away from the split vertex, side membership of a source vertex gives
component membership of every outgoing dart at that vertex. -/
theorem splitSide_source_membership (a b : G.Dart) (hab : a.fst = b.fst)
    (hne : a ≠ b) (mark d : G.Dart) (haway : d.fst ≠ a.fst)
    (hmem : d.fst ∈ R.splitSide a b hab mark) :
    (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) d)
      (RefinedRotation.vertex G (R.splitRotation a b) mark) := by
  obtain ⟨e,he,hr⟩ := hmem
  have hq : RefinedRotation.vertex G (R.splitRotation a b) d =
      RefinedRotation.vertex G (R.splitRotation a b) e :=
    Quotient.sound (R.split_cycles_away a b hab hne d e haway he.symm)
  rw [hq]
  exact hr

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A boundary vertex other than the removed vertex and its predecessor
has an actual surviving old boundary dart with that source. -/
theorem old_boundary_surviving_dart (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (u : V) (hu : u ∈ R.facialVertices outer)
    (hv : u ≠ outer.snd) (hp : u ≠ outer.fst) :
    ∃ z : (VertexDeletedGraph (G := G) outer.snd).Dart,
      R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val ∧ z.fst.val = u := by
  obtain ⟨a,ha,hs⟩ := hu
  have hsrc : a.fst ≠ outer.snd := hs ▸ hv
  have htgt : a.snd ≠ outer.snd := by
    intro ht
    have he := R.face.injective (hsimple (R.face a) (R.face outer) ha.apply_right
      Equiv.Perm.SameCycle.rfl.apply_right (by rw [R.face_source,R.face_source,ht]))
    exact hp (hs.symm.trans (congrArg (fun z : G.Dart => z.fst) he))
  let z := (vertexDeletedDartEquiv outer.snd).symm ⟨a,hsrc,htgt⟩
  refine ⟨z,?_,hs⟩
  change R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd)
    ((vertexDeletedDartEquiv outer.snd).symm _)).val
  rw [Equiv.apply_symm_apply]
  exact ha

/-- An old outer dart in the chosen component, excluded from the restoration
path, gives a retained boundary vertex on the actual induced side. -/
theorem splitSideDart_residual_vertex (a b : G.Dart) (hab : a.fst = b.fst)
    (hne : a ≠ b) (hc : G.Preconnected) (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)
    (mark root d : G.Dart) (hr hd)
    (hroot : R.face.SameCycle a root) (houter : R.face.SameCycle a d)
    (n : ℕ) (p : Fin n → G.Dart)
    (hp : ∀ i, (RefinedRotation.graph G (R.splitRotation a b) (R.split_source a b hab)).Reachable
      (RefinedRotation.vertex G (R.splitRotation a b) (p i))
      (RefinedRotation.vertex G (R.splitRotation a b) mark))
    (hnot : ∀ i, d ≠ p i) :
    let T := R.splitSideRotation a b hab hne hc hz hf mark
    let r := R.splitSideDart a b hab mark root hr
    let z := R.splitSideDart a b hab mark d hd
    let ds := List.ofFn (fun i => R.splitSideDart a b hab mark (p i) (hp i))
    ResidualBoundaryVertex (G.induce (R.splitSide a b hab mark)) T (T.face.symm r).symm ds z.fst := by
  dsimp only
  refine ⟨R.splitSideDart a b hab mark d hd,?_,?_,rfl⟩
  · have hh := (R.splitSideDart_face_cycles a b hab hne hc hz hf mark root d hr hd).mpr
      (R.split_outer_same_component a b hab hne hc hz hf root d hroot houter (hr.trans hd.symm))
    simpa only [SimpleGraph.Dart.symm_symm] using hh.symm_apply_left
  · intro hm
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    exact hnot i (R.splitSideDart_injective a b hab mark d (p i) hd (hp i) hi.symm)

end JSP512Probe.RotationSystem
