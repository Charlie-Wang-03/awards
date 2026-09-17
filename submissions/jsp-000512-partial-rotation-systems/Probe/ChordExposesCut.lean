import Probe.DiskDeletionGenus
import Probe.SplitSeparation

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- A genuine boundary chord exposes two distinct occurrences of its surviving
endpoint on the new outer face after the other endpoint is deleted. -/
theorem chord_exposes_sector_vertex (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b → a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (root : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hr : ∀ x, (R.deleteVertex outer.snd).face.SameCycle root x ↔ R.outerDeletionRegion outer x)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    ∃ x y : (VertexDeletedGraph (G := G) outer.snd).Dart,
      (R.deleteVertex outer.snd).face.SameCycle root x ∧
      (R.deleteVertex outer.snd).face.SameCycle root y ∧
      x ≠ y ∧ x.fst = y.fst ∧ x.fst.val = a.fst ∧
      R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val ∧
      ¬R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) y).val ∧
      ∃ (d : G.Dart) (hd : d.fst = outer.snd)
        (ht : R.face (R.face (R.face d.symm)) = d.symm),
        d ≠ outer.symm ∧ R.rotate d ≠ outer.symm ∧
        y = R.sectorDeletedDart outer.snd d hd ht := by
  have has : a.fst ≠ outer.snd := hadj.ne.symm
  have hat : a.snd ≠ outer.snd := by
    intro h
    have he := R.face.injective (hsimple (R.face a) (R.face outer) ha.apply_right
      Equiv.Perm.SameCycle.rfl.apply_right (by rw [R.face_source,R.face_source,h]))
    exact hleft (congrArg (fun d : G.Dart => d.fst) he)
  let x := (vertexDeletedDartEquiv outer.snd).symm ⟨a,has,hat⟩
  have hxl : ((vertexDeletedDartEquiv outer.snd) x).val = a := by
    change ((vertexDeletedDartEquiv outer.snd) ((vertexDeletedDartEquiv outer.snd).symm _)).val = a
    rw [Equiv.apply_symm_apply]
  have hx : (R.deleteVertex outer.snd).face.SameCycle root x := (hr x).mpr (Or.inl (by
    rw [hxl]; exact ha))
  let e : G.Dart := ⟨(outer.snd,a.fst),hadj⟩
  let d := R.rotate.symm e
  have he : R.rotate d = e := R.rotate.apply_symm_apply _
  have hd : d.fst = outer.snd := by
    have hh := R.source d
    rw [he] at hh
    exact hh.symm
  have hne : d ≠ outer.symm := by
    intro h
    have hh : R.face outer = e := by change R.rotate outer.symm = e; rwa [h] at he
    exact hright (congrArg (fun d : G.Dart => d.snd) hh).symm
  have ht := R.outer_face_fan outer hsimple hinner d hd hne
  have hn : ¬R.face.SameCycle outer d.symm := by
    intro h
    have hh := R.face.injective (hsimple (R.face d.symm) (R.face outer) h.apply_right
      Equiv.Perm.SameCycle.rfl.apply_right (by rw [R.face_source,R.face_source]; exact hd))
    apply hne
    simpa only [SimpleGraph.Dart.symm_symm] using congrArg SimpleGraph.Dart.symm hh
  let y := R.sectorDeletedDart outer.snd d hd ht
  have hyl : ((vertexDeletedDartEquiv outer.snd) y).val = R.face (R.rotate d) := by
    change ((vertexDeletedDartEquiv outer.snd) ((vertexDeletedDartEquiv outer.snd).symm _)).val = _
    rw [Equiv.apply_symm_apply]
  have hy : (R.deleteVertex outer.snd).face.SameCycle root y := by
    apply (hr y).mpr
    right
    rw [hyl]
    have hf : R.face d.symm = R.rotate d := by
      change R.rotate d.symm.symm = R.rotate d
      rw [SimpleGraph.Dart.symm_symm]
    rw [hf] at ht
    rw [ht]
    exact hd
  have hys : y.fst.val = a.fst := by
    change (R.face (R.rotate d)).fst = a.fst
    rw [R.face_source,he]
  have hrot : R.rotate d ≠ outer.symm := by
    rw [he]
    intro hh
    exact hleft (congrArg (fun z : G.Dart => z.snd) hh)
  refine ⟨x,y,hx,hy,?_,Subtype.ext (show x.fst.val = y.fst.val from hys.symm),rfl,
    by rw [hxl]; exact ha,
    by rw [hyl]; exact R.inner_sector_not_outer outer d hn,
    ⟨d,hd,ht,hne,hrot,rfl⟩⟩
  intro h
  have hh := congrArg (fun z => ((vertexDeletedDartEquiv outer.snd) z).val) h
  rw [hxl,hyl] at hh
  exact R.inner_sector_not_outer outer d hn (hh ▸ ha)
/-- Compatibility projection retaining the original marked-cut interface. -/
theorem chord_exposes_marked_vertex (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b → a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (root : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hr : ∀ x, (R.deleteVertex outer.snd).face.SameCycle root x ↔ R.outerDeletionRegion outer x)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    ∃ x y : (VertexDeletedGraph (G := G) outer.snd).Dart,
      (R.deleteVertex outer.snd).face.SameCycle root x ∧
      (R.deleteVertex outer.snd).face.SameCycle root y ∧
      x ≠ y ∧ x.fst = y.fst ∧ x.fst.val = a.fst ∧
      R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val ∧
      ¬R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) y).val := by
  obtain ⟨x,y,hx,hy,hne,hxy,hu,hxo,hyo,_⟩ :=
    R.chord_exposes_sector_vertex outer hsimple hinner root hr a ha hadj hleft hright
  exact ⟨x,y,hx,hy,hne,hxy,hu,hxo,hyo⟩

/-- Compatibility projection of the marked chord exposure. -/
theorem chord_exposes_repeated_vertex (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b → a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (root : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hr : ∀ x, (R.deleteVertex outer.snd).face.SameCycle root x ↔ R.outerDeletionRegion outer x)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    ∃ x y : (VertexDeletedGraph (G := G) outer.snd).Dart,
      (R.deleteVertex outer.snd).face.SameCycle root x ∧
      (R.deleteVertex outer.snd).face.SameCycle root y ∧
      x ≠ y ∧ x.fst = y.fst ∧ x.fst.val = a.fst := by
  obtain ⟨x,y,hx,hy,hne,hxy,hu,_,_⟩ :=
    R.chord_exposes_marked_vertex outer hsimple hinner root hr a ha hadj hleft hright
  exact ⟨x,y,hx,hy,hne,hxy,hu⟩

/-- Delete one chord endpoint and split the exposed other endpoint: this
constructs an actual zero-genus graph with exactly two components. -/
theorem chord_deletion_separates (outer : G.Dart) (hz : R.HasGenusZero)
    (hc : G.Preconnected)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b → a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    ∃ (x y : (VertexDeletedGraph (G := G) outer.snd).Dart) (hxy : x.fst = y.fst),
      x ≠ y ∧ x.fst.val = a.fst ∧
      let S := R.deleteVertex outer.snd
      let H := VertexDeletedGraph (G := G) outer.snd
      letI : Fintype (RefinedRotation.Vertex H (S.splitRotation x y)) := Fintype.ofFinite _
      Nat.card (RefinedRotation.graph H (S.splitRotation x y)
        (S.split_source x y hxy)).ConnectedComponent = 2 ∧
      (RefinedRotation.rotation H (S.splitRotation x y) (S.split_source x y hxy)).HasGenusZero := by
  classical
  obtain ⟨root,hr⟩ := R.outer_region_single_orbit outer hsimple hinner hcorner
  obtain ⟨x,y,hx,hy,hne,hxy,hu⟩ :=
    R.chord_exposes_repeated_vertex outer hsimple hinner root hr a ha hadj hleft hright
  have hs := R.boundary_deleteVertex_genusZero outer hz hc hsimple hinner hcorner
  have hconn := R.outer_vertex_deleted_connected outer hc hsimple hinner
  exact ⟨x,y,hxy,hne,hu,(R.deleteVertex outer.snd).split_separates_genusZero
    x y hxy hne hconn.preconnected hs (hx.symm.trans hy)⟩

end JSP512Probe.RotationSystem
