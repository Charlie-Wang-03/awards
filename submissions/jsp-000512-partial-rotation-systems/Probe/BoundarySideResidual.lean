import Probe.ExposedSideResidual

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Actual boundary premises for restoring the old-boundary side. Its attachment
is the original predecessor of the removed boundary vertex. -/
theorem boundary_side_residual_conditions (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart) (hxy : x.fst = y.fst)
    (hne : x ≠ y) (hc : (VertexDeletedGraph (G := G) outer.snd).Preconnected)
    (hz : (R.deleteVertex outer.snd).HasGenusZero)
    (hf : (R.deleteVertex outer.snd).face.SameCycle x y)
    (hregion : ∀ z, (R.deleteVertex outer.snd).face.SameCycle x z → R.outerDeletionRegion outer z)
    (n m : ℕ) (f : Fin n → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (g : Fin (m+1) → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hroot : (R.deleteVertex outer.snd).face.SameCycle x (g 0))
    (hsource : (g 0).fst.val = outer.fst)
    (hcover : ∀ z, R.outerDeletionRegion outer z →
      R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val ∨
        (∃ i, z = f i) ∨ (∃ j, z = g j)) :
    let S := R.deleteVertex outer.snd
    let H := RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)
    let q := RefinedRotation.vertex _ (S.splitRotation x y)
    ∀ (_hfr : ∀ i, H.Reachable (q (f i)) (q y))
      (hgr : ∀ j, H.Reachable (q (g j)) (q x)),
      let T := S.splitSideRotation x y hxy hne hc hz hf x
      let root := S.splitSideDart x y hxy x (g 0) (hgr 0)
      let anchor := (T.face.symm root).symm
      let ds := List.ofFn (fun i => S.splitSideDart x y hxy x (g i) (hgr i))
      ResidualBoundarySimple ((VertexDeletedGraph (G := G) outer.snd).induce
        (S.splitSide x y hxy x)) T anchor ds ∧
      ∀ z, T.face.SameCycle anchor.symm z → z ∉ ds → z.fst ≠ anchor.fst := by
  dsimp only
  intro hfr hgr
  let S := R.deleteVertex outer.snd
  let H := RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)
  let q := RefinedRotation.vertex _ (S.splitRotation x y)
  let P := fun z => R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val ∧
    H.Reachable (q z) (q x)
  have hret := (R.split_residual_old_boundary outer x y hxy hne hc hz hf f g hcover hfr hgr).1
  exact S.splitSideDart_residual_conditions x y hxy hne hc hz hf x (g 0)
    (hgr 0) hroot (m+1) g hgr P
    (fun z hr ho hn => ⟨hret z (hregion z ho) hr hn,hr⟩)
    (fun d e hd he hh => R.old_boundary_survivors_simple outer hsimple d e hd.1 he.1 hh)
    (fun z hzold heq => R.old_boundary_avoids_attachment outer hsimple z hzold.1
      ((congrArg Subtype.val heq).trans hsource))

end JSP512Probe.RotationSystem
