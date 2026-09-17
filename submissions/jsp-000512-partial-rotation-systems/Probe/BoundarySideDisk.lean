import Probe.BoundarySideResidual
import Probe.SplitSideChosenOuter
import Probe.FanStartDisk

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Restore the old-boundary split side as an actual triangulated disk, retaining
exact edge and boundary-vertex descriptions. -/
theorem boundary_side_disk_edges (outer : G.Dart)
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
    (hstep : ∀ i : Fin m, (R.deleteVertex outer.snd).face (g i.castSucc) = g i.succ)
    (hcutx : ∀ i : Fin m, g i.succ ≠ x) (hcuty : ∀ i : Fin m, g i.succ ≠ y)
    (htarget : Function.Injective (fun i => (g i).snd))
    (havoid : ∀ i, (g i).snd ≠ (g 0).fst)
    (hi : ∀ z, ¬(R.deleteVertex outer.snd).face.SameCycle x z →
      (R.deleteVertex outer.snd).face ((R.deleteVertex outer.snd).face
        ((R.deleteVertex outer.snd).face z)) = z)
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
      let A := S.splitSide x y hxy x
      letI : Fintype A := Fintype.ofFinite _
      let J := (VertexDeletedGraph (G := G) outer.snd).induce A
      ∃ K : SimpleGraph (Option A),
        (∀ u v, K.Adj (some u) (some v) ↔ J.Adj u v) ∧
        (∀ u, K.Adj none (some u) ↔ u = anchor.fst ∨ ∃ d ∈ ds, d.snd = u) ∧
        ∃ U : RotationSystem K, ∃ c : K.Dart,
          c.toProd = (none, some anchor.fst) ∧ U.IsTriangulatedDisk c.symm ∧
          (∀ u, u ∈ U.facialVertices c.symm ↔
            u = none ∨ u = some anchor.fst ∨
              ∃ v, u = some v ∧ ResidualBoundaryVertex J T anchor ds v) ∧
          ∀ d : J.Dart, T.face.SameCycle anchor.symm d → d ∉ ds →
            ∃ e : K.Dart, e.toProd = (some d.fst,some d.snd) ∧ U.face.SameCycle c.symm e := by
  classical
  dsimp only
  intro hfr hgr
  let S := R.deleteVertex outer.snd
  let A := S.splitSide x y hxy x
  let : Fintype A := Fintype.ofFinite _
  let J := (VertexDeletedGraph (G := G) outer.snd).induce A
  let T := S.splitSideRotation x y hxy hne hc hz hf x
  let p := fun i => S.splitSideDart x y hxy x (g i) (hgr i)
  let anchor := (T.face.symm (p 0)).symm
  have hres := R.boundary_side_residual_conditions outer hsimple x y hxy hne hc hz hf
    hregion n m f g hroot hsource hcover hfr hgr
  apply startFan_disk_edges J T anchor (List.ofFn p)
  · change FaceRoute T.face (T.face.symm (p 0)) (List.ofFn p)
    rw [List.ofFn_succ]
    exact ⟨T.face.apply_symm_apply _,
      S.splitSideDart_route x y hxy hne hc hz hf x m g hgr hstep hcutx hcuty⟩
  · apply List.pairwise_ofFn.mpr
    intro i j hij heq
    exact (ne_of_lt hij) (htarget (congrArg Subtype.val heq))
  · intro z hmem heq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
    apply havoid i
    have hh : (p i).snd = (T.face.symm (p 0)).snd := heq
    rw [T.face_inverse_target] at hh
    exact congrArg Subtype.val hh
  · exact S.splitSideRotation_genusZero x y hxy hne hc hz hf x
  · exact S.splitSide_connected x y hxy x
  · exact S.splitSideDart_anchor_inner x y hxy hne hc hz hf x (g 0) (hgr 0) hroot hi
  · exact hres.1
  · exact hres.2

/-- Compatibility projection of boundary-side disk restoration with old edges. -/
theorem boundary_side_disk (outer : G.Dart)
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
    (hstep : ∀ i : Fin m, (R.deleteVertex outer.snd).face (g i.castSucc) = g i.succ)
    (hcutx : ∀ i : Fin m, g i.succ ≠ x) (hcuty : ∀ i : Fin m, g i.succ ≠ y)
    (htarget : Function.Injective (fun i => (g i).snd))
    (havoid : ∀ i, (g i).snd ≠ (g 0).fst)
    (hi : ∀ z, ¬(R.deleteVertex outer.snd).face.SameCycle x z →
      (R.deleteVertex outer.snd).face ((R.deleteVertex outer.snd).face
        ((R.deleteVertex outer.snd).face z)) = z)
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
      let A := S.splitSide x y hxy x
      letI : Fintype A := Fintype.ofFinite _
      let J := (VertexDeletedGraph (G := G) outer.snd).induce A
      ∃ K : SimpleGraph (Option A),
        (∀ u v, K.Adj (some u) (some v) ↔ J.Adj u v) ∧
        (∀ u, K.Adj none (some u) ↔ u = anchor.fst ∨ ∃ d ∈ ds, d.snd = u) ∧
        ∃ U : RotationSystem K, ∃ c : K.Dart,
          c.toProd = (none, some anchor.fst) ∧ U.IsTriangulatedDisk c.symm ∧
          ∀ u, u ∈ U.facialVertices c.symm ↔
            u = none ∨ u = some anchor.fst ∨
              ∃ v, u = some v ∧ ResidualBoundaryVertex J T anchor ds v := by
  classical
  dsimp only
  intro hfr hgr
  obtain ⟨K,hold,hcenter,U,c,hca,hD,hverts,_⟩ :=
    R.boundary_side_disk_edges outer hsimple x y hxy hne hc hz hf hregion
      n m f g hroot hsource hstep hcutx hcuty htarget havoid hi hcover hfr hgr
  exact ⟨K,hold,hcenter,U,c,hca,hD,hverts⟩

end JSP512Probe.RotationSystem
