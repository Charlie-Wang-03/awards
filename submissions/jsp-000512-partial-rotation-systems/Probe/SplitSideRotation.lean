import Probe.RotationIso
import Probe.SplitSideIso

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (a b : G.Dart) (hab : a.fst = b.fst)
  (hne : a ≠ b) (hc : G.Preconnected) (hz : R.HasGenusZero) (hf : R.face.SameCycle a b)

/-- The actual rotation on the induced old-vertex side, obtained by component
restriction followed by the proved component-to-side graph isomorphism. -/
noncomputable def splitSideRotation (mark : G.Dart) : RotationSystem (G.induce (R.splitSide a b hab mark)) := by
  classical
  let σ := R.splitRotation a b
  let : Fintype (RefinedRotation.Vertex G σ) := Fintype.ofFinite _
  let H := RefinedRotation.graph G σ (R.split_source a b hab)
  let S := RefinedRotation.rotation G σ (R.split_source a b hab)
  let C := H.connectedComponentMk (RefinedRotation.vertex G σ mark)
  let : Fintype C := Fintype.ofFinite _
  exact (S.componentRotation C).mapIso (R.split_component_iso a b hab hne hc hz hf mark)

/-- The actual induced-side rotation has zero genus. -/
theorem splitSideRotation_genusZero (mark : G.Dart) :
    letI : Fintype (R.splitSide a b hab mark) := Fintype.ofFinite _
    (R.splitSideRotation a b hab hne hc hz hf mark).HasGenusZero := by
  classical
  let σ := R.splitRotation a b
  let : Fintype (RefinedRotation.Vertex G σ) := Fintype.ofFinite _
  let H := RefinedRotation.graph G σ (R.split_source a b hab)
  let S := RefinedRotation.rotation G σ (R.split_source a b hab)
  let C := H.connectedComponentMk (RefinedRotation.vertex G σ mark)
  let : Fintype C := Fintype.ofFinite _
  let : Fintype (R.splitSide a b hab mark) := Fintype.ofFinite _
  change ((S.componentRotation C).mapIso (R.split_component_iso a b hab hne hc hz hf mark)).HasGenusZero
  apply mapIso_genusZero
  exact S.componentRotation_genusZero (R.split_separates_genusZero a b hab hne hc hz hf).2 C
end JSP512Probe.RotationSystem
