import Probe.ExposedSideResidual
import Probe.SplitSideChosenOuter
import Probe.FanStartDisk

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Restore the exposed split side as an actual triangulated disk, retaining
exact edge and boundary-vertex descriptions. -/
theorem exposed_side_disk (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart) (hxy : x.fst = y.fst)
    (hne : x ≠ y) (hc : (VertexDeletedGraph (G := G) outer.snd).Preconnected)
    (hz : (R.deleteVertex outer.snd).HasGenusZero)
    (hf : (R.deleteVertex outer.snd).face.SameCycle x y)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (hregion : ∀ z, (R.deleteVertex outer.snd).face.SameCycle x z → R.outerDeletionRegion outer z)
    (n m : ℕ) (f : Fin (n+1) → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (g : Fin m → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hstart : f 0 = y)
    (hstep : ∀ i : Fin n, (R.deleteVertex outer.snd).face (f i.castSucc) = f i.succ)
    (hcutx : ∀ i : Fin n, f i.succ ≠ x) (hcuty : ∀ i : Fin n, f i.succ ≠ y)
    (htarget : Function.Injective (fun i => (f i).snd))
    (havoid : ∀ i, (f i).snd ≠ (f 0).fst)
    (hi : ∀ z, ¬(R.deleteVertex outer.snd).face.SameCycle x z →
      (R.deleteVertex outer.snd).face ((R.deleteVertex outer.snd).face
        ((R.deleteVertex outer.snd).face z)) = z)
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
      let A := S.splitSide x y hxy y
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
  subst y
  let S := R.deleteVertex outer.snd
  let A := S.splitSide x (f 0) hxy (f 0)
  let : Fintype A := Fintype.ofFinite _
  let J := (VertexDeletedGraph (G := G) outer.snd).induce A
  let T := S.splitSideRotation x (f 0) hxy hne hc hz hf (f 0)
  let p := fun i => S.splitSideDart x (f 0) hxy (f 0) (f i) (hfr i)
  let anchor := (T.face.symm (p 0)).symm
  have hres := R.exposed_side_residual_conditions outer hsimple x (f 0) hxy hne hc hz hf hx
    hregion (n+1) m f g hcover hfr hgr
  apply startFan_disk J T anchor (List.ofFn p)
  · change FaceRoute T.face (T.face.symm (p 0)) (List.ofFn p)
    rw [List.ofFn_succ]
    exact ⟨T.face.apply_symm_apply _,
      S.splitSideDart_route x (f 0) hxy hne hc hz hf (f 0) n f hfr hstep hcutx hcuty⟩
  · apply List.pairwise_ofFn.mpr
    intro i j hij heq
    exact (ne_of_lt hij) (htarget (congrArg Subtype.val heq))
  · intro z hmem heq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
    apply havoid i
    have hh : (p i).snd = (T.face.symm (p 0)).snd := heq
    rw [T.face_inverse_target] at hh
    exact congrArg Subtype.val hh
  · exact S.splitSideRotation_genusZero x (f 0) hxy hne hc hz hf (f 0)
  · exact S.splitSide_connected x (f 0) hxy (f 0)
  · exact S.splitSideDart_anchor_inner x (f 0) hxy hne hc hz hf (f 0) (f 0) (hfr 0) hf hi
  · exact hres.1
  · exact hres.2

end JSP512Probe.RotationSystem
