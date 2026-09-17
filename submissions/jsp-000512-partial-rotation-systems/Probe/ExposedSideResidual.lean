import Probe.SplitSideResidualTransport
import Probe.SectorResidualBoundary

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Actual boundary premises for restoring the exposed-sector side. Both
residual source simplicity and exclusion of the chord attachment are derived
from the original boundary and separation of the two sector paths. -/
theorem exposed_side_residual_conditions (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart) (hxy : x.fst = y.fst)
    (hne : x ≠ y) (hc : (VertexDeletedGraph (G := G) outer.snd).Preconnected)
    (hz : (R.deleteVertex outer.snd).HasGenusZero)
    (hf : (R.deleteVertex outer.snd).face.SameCycle x y)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (hregion : ∀ z, (R.deleteVertex outer.snd).face.SameCycle x z → R.outerDeletionRegion outer z)
    (n m : ℕ) (f : Fin n → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (g : Fin m → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hcover : ∀ z, R.outerDeletionRegion outer z →
      R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val ∨
        (∃ i, z = f i) ∨ (∃ j, z = g j)) :
    let S := R.deleteVertex outer.snd
    let H := RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)
    let q := RefinedRotation.vertex _ (S.splitRotation x y)
    ∀ (hfr : ∀ i, H.Reachable (q (f i)) (q y))
      (_hgr : ∀ j, H.Reachable (q (g j)) (q x)),
      let T := S.splitSideRotation x y hxy hne hc hz hf y
      let root := S.splitSideDart x y hxy y y SimpleGraph.Reachable.rfl
      let anchor := (T.face.symm root).symm
      let ds := List.ofFn (fun i => S.splitSideDart x y hxy y (f i) (hfr i))
      ResidualBoundarySimple ((VertexDeletedGraph (G := G) outer.snd).induce
        (S.splitSide x y hxy y)) T anchor ds ∧
      ∀ z, T.face.SameCycle anchor.symm z → z ∉ ds → z.fst ≠ anchor.fst := by
  dsimp only
  intro hfr hgr
  let S := R.deleteVertex outer.snd
  let H := RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)
  let q := RefinedRotation.vertex _ (S.splitRotation x y)
  let P := fun z => R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val ∧
    H.Reachable (q z) (q y)
  have hret := (R.split_residual_old_boundary outer x y hxy hne hc hz hf f g hcover hfr hgr).2
  exact S.splitSideDart_residual_conditions x y hxy hne hc hz hf y y
    SimpleGraph.Reachable.rfl hf n f hfr P
    (fun z hr ho hn => ⟨hret z (hregion z ho) hr hn,hr⟩)
    (fun d e hd he hh => R.old_boundary_survivors_simple outer hsimple d e hd.1 he.1 hh)
    (fun z hzold => R.old_boundary_avoids_other_cut outer hsimple x y hxy hne hc hz hf hx z
      hzold.1 hzold.2)

end JSP512Probe.RotationSystem
