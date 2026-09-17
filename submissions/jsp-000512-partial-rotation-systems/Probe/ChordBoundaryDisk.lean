import Probe.ChordExposedDisk
import Probe.BoundarySideDisk
import Probe.ChordIncomingEdge

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {R : RotationSystem G}
  {outer : G.Dart} {w : V}

namespace ChordSectorData

/-- Coherent chord data constructs a disk on the original restored induced
side, with the original outer dart as the distinguished boundary edge. -/
theorem boundary_disk_boundary_edges (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a) :
    letI : Fintype (restoreSide outer.snd D.boundarySide) := Fintype.ofFinite _
    ∃ U : RotationSystem (G.induce (restoreSide outer.snd D.boundarySide)),
      ∃ c, U.IsTriangulatedDisk c ∧ c.fst.val = outer.fst ∧ c.snd.val = outer.snd ∧
        (∀ u, u.val ∈ R.facialVertices outer → u ∈ U.facialVertices c) ∧
        ∀ pre : G.Dart, R.face.SameCycle outer pre → pre.snd = outer.fst →
          pre.fst ≠ outer.snd → ∃ e, U.face.SameCycle c e ∧
            e.fst.val = pre.fst ∧ e.snd.val = pre.snd := by
  classical
  let S := R.deleteVertex outer.snd
  let f := D.firstPath
  let g := D.secondPath
  have hxy : D.x.fst = (f 0).fst := D.cut_source.trans (congrArg (fun z => z.fst) D.sector_cut)
  have hne : D.x ≠ f 0 := by simpa only [D.sector_cut, f, firstPath, S] using D.cut_ne
  have hf : S.face.SameCycle D.x (f 0) := by simpa only [D.sector_cut, f, firstPath, S] using D.cut_face
  have hcuts := R.chord_sector_cut_avoidance outer hsimple D.x D.old_cut D.n D.d
    D.d_source D.d_triangle D.d_avoid D.d_injective
  have hstep : ∀ i : Fin D.n, S.face (f i.castSucc) = f i.succ := by
    intro i
    exact R.sector_predecessor_step outer.snd _ _ _ _ (D.d_step i) _ _
  have hfr := S.split_path_in_component D.x (f 0) hxy (f 0) D.n f
    SimpleGraph.Reachable.rfl hstep (fun i => hcuts.1 i.succ) hcuts.2
  have hgr := R.complementary_sector_side outer hsimple D.x D.old_cut (D.d 0)
    (D.d_source 0) (D.d_triangle 0) D.m D.e D.e_source D.e_triangle
    (fun j => (D.e_avoid j).1) (fun j => (D.e_avoid j).2) D.e_step D.e_end hxy
  have hgstep : ∀ i : Fin D.m, S.face (g i.castSucc) = g i.succ := by
    intro i
    exact R.sector_predecessor_step outer.snd _ _ _ _ (D.e_step i) _ _
  have hgcutx : ∀ i : Fin D.m, g i.succ ≠ D.x := by
    intro i heq
    change R.sectorDeletedDart outer.snd (D.e i.succ) _ _ = D.x at heq
    exact R.deleted_sector_not_old_outer outer hsimple _ (D.e_source i.succ)
      (D.e_avoid i.succ).1 (D.e_triangle i.succ) (heq.symm ▸ D.old_cut)
  have hgcuty : ∀ i : Fin D.m, g i.succ ≠ f 0 := by
    intro i heq
    exact (D.e_avoid i.succ).2 (R.sector_target_injective outer.snd _ _ _ _ _ _
      (congrArg (fun z : (VertexDeletedGraph (G := G) outer.snd).Dart => z.snd) heq))
  have htarget : Function.Injective (fun i => (g i).snd) := by
    intro i j he
    exact D.e_injective (R.sector_target_injective outer.snd _ _ _ _ _ _ he)
  have havoid := R.sector_interval_source_avoidance outer.snd D.m D.e D.e_source D.e_triangle
    D.e_step D.e_injective (D.d 0) D.e_end (D.e_avoid 0).2.symm
  have hroot : S.face.SameCycle D.x (g 0) := by
    apply hf.trans
    exact R.outer_fan_single_orbit outer
      (fun d hd hn => R.outer_face_fan outer hsimple hinner d hd hn)
      (D.e 0) (D.e_source 0) (D.e_avoid 0).1 D.e_start
      (D.d 0) (D.d_source 0) (D.d_avoid 0)
  have hsource : (g 0).fst.val = outer.fst := by
    change (R.face (R.rotate (D.e 0))).fst = outer.fst
    rw [R.face_source,D.e_start]
    rfl
  have hcover := R.outer_region_path_cover outer hinner D.n D.m D.d D.e D.d_source D.e_source
    D.d_triangle D.e_triangle D.d_step D.e_step D.d_end D.e_start D.e_end
  let A := S.splitSide D.x (f 0) hxy D.x
  let : Fintype A := Fintype.ofFinite _
  let : Fintype (restoreSide outer.snd A) := Fintype.ofFinite _
  let T := S.splitSideRotation D.x (f 0) hxy hne D.connected.preconnected D.zero hf D.x
  let p := fun i => S.splitSideDart D.x (f 0) hxy D.x (g i) (hgr i)
  obtain ⟨K,hold,hcenter,U,c,hc,hD,hverts,hedge⟩ := R.boundary_side_disk_edges outer hsimple
    D.x (f 0) hxy hne D.connected.preconnected D.zero hf
    (fun z hz => (D.region z).mp hz) (D.n+1) D.m f g hroot hsource hgstep
    hgcutx hgcuty htarget havoid D.inner hcover hfr hgr
  have hneighbors := (R.chord_sector_neighbors outer hsimple D.x D.old_cut D.n D.m D.d D.e
    D.d_source D.e_source D.d_triangle D.e_triangle D.d_avoid (fun j => (D.e_avoid j).1)
    (fun j => (D.e_avoid j).2) D.d_injective D.d_step D.e_step D.d_end D.e_start D.e_end
    hxy D.connected.preconnected D.zero hf).1
  let E := restoredRouteIso G outer.snd A T (p 0) (D.m+1) p K hold hcenter
    (fun u => hneighbors u.val u.property)
  refine ⟨U.mapIso E,isoDarts E c.symm,U.mapIso_disk E c.symm hD,?_,?_,?_,?_⟩
  · have ha : ((T.face.symm (p 0)).symm.fst).val.val = outer.fst := by
      change (T.face.symm (p 0)).snd.val.val = outer.fst
      rw [T.face_inverse_target]
      exact hsource
    change (E c.snd).val = outer.fst
    have he : c.snd = some (T.face.symm (p 0)).symm.fst := congrArg Prod.snd hc
    rw [he]
    exact ha
  · change (E c.fst).val = outer.snd
    have he : c.fst = none := congrArg Prod.fst hc
    rw [he]
    rfl
  · intro u hu
    obtain ⟨z,rfl⟩ := E.surjective u
    apply (U.mapIso_facialVertices E c.symm z).mpr
    apply (hverts z).mpr
    cases z with
    | none => exact Or.inl rfl
    | some u =>
      change u.val.val ∈ R.facialVertices outer at hu
      have ha : (T.face.symm (p 0)).symm.fst = (p 0).fst := T.face_inverse_target _
      have hpath := fun i => R.deleted_sector_not_old_outer outer hsimple _ (D.e_source i)
        (D.e_avoid i).1 (D.e_triangle i)
      by_cases he : u.val.val = outer.fst
      · right; left
        apply congrArg some
        rw [ha]
        exact Subtype.ext (Subtype.ext (he.trans hsource.symm))
      · right; right
        refine ⟨u,rfl,?_⟩
        by_cases hcut : u.val = D.x.fst
        · have hh := R.old_cut_side_residual outer D.x (f 0) hxy hne
            D.connected.preconnected D.zero hf D.old_cut (g 0) hroot (D.m+1) g hpath
            (hgr 0) hgr
          dsimp only at hh
          have heq : (S.splitSideDart D.x (f 0) hxy D.x D.x
              SimpleGraph.Reachable.rfl).fst = u := Subtype.ext hcut.symm
          rw [heq] at hh
          exact hh
        · exact R.old_boundary_side_residual outer hsimple D.x (f 0) hxy hne
            D.connected.preconnected D.zero hf (fun z hz => (D.region z).mpr hz)
            D.x (g 0) hroot (D.m+1) g hpath (hgr 0) hgr u.val u.property hu he hcut

  · intro pre hpre ht hs
    have htne : pre.snd ≠ outer.snd := by
      rw [ht]
      exact outer.adj.ne
    let z := (vertexDeletedDartEquiv outer.snd).symm ⟨pre,hs,htne⟩
    have hzlift : ((vertexDeletedDartEquiv outer.snd) z).val = pre := by
      exact congrArg Subtype.val ((vertexDeletedDartEquiv outer.snd).apply_symm_apply _)
    have hzt : z.snd.val = outer.fst := ht
    have hzr := D.incoming_component hsimple z hzt
    have hzo : S.face.SameCycle D.x z := (D.region z).mpr (Or.inl (hzlift ▸ hpre))
    let zd := S.splitSideDart D.x (f 0) hxy D.x z hzr
    have hzouter : T.face.SameCycle (T.face.symm (p 0)) zd := by
      have hh := (S.splitSideDart_face_cycles D.x (f 0) hxy hne
        D.connected.preconnected D.zero hf D.x (g 0) z (hgr 0) hzr).mpr
        (S.split_outer_same_component D.x (f 0) hxy hne
          D.connected.preconnected D.zero hf (g 0) z hroot hzo ((hgr 0).trans hzr.symm))
      exact hh.symm_apply_left
    have hznot : zd ∉ List.ofFn p := by
      intro hm
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      have he := S.splitSideDart_injective D.x (f 0) hxy D.x z (g i) hzr (hgr i) hi.symm
      have ho : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val := hzlift ▸ hpre
      rw [he] at ho
      exact R.deleted_sector_not_old_outer outer hsimple _ (D.e_source i)
        (D.e_avoid i).1 (D.e_triangle i) ho
    obtain ⟨e,he,heo⟩ := hedge zd hzouter hznot
    refine ⟨isoDarts E e,(U.mapIso_face_cycles E c.symm e).mpr heo,?_,?_⟩
    · change (E e.fst).val = pre.fst
      have hh := congrArg Prod.fst he
      rw [hh]
      rfl
    · change (E e.snd).val = pre.snd
      have hh := congrArg Prod.snd he
      rw [hh]
      rfl

/-- Compatibility projection retaining the boundary-vertex interface. -/
theorem boundary_disk_boundary (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a) :
    letI : Fintype (restoreSide outer.snd D.boundarySide) := Fintype.ofFinite _
    ∃ U : RotationSystem (G.induce (restoreSide outer.snd D.boundarySide)),
      ∃ c, U.IsTriangulatedDisk c ∧ c.fst.val = outer.fst ∧ c.snd.val = outer.snd ∧
        ∀ u, u.val ∈ R.facialVertices outer → u ∈ U.facialVertices c := by
  obtain ⟨U,c,hD,hs,ht,hb,_⟩ := D.boundary_disk_boundary_edges hsimple hinner
  exact ⟨U,c,hD,hs,ht,hb⟩

/-- Compatibility projection of the boundary-preserving disk construction. -/
theorem boundary_disk (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a) :
    letI : Fintype (restoreSide outer.snd D.boundarySide) := Fintype.ofFinite _
    ∃ U : RotationSystem (G.induce (restoreSide outer.snd D.boundarySide)),
      ∃ c, U.IsTriangulatedDisk c ∧ c.fst.val = outer.fst ∧ c.snd.val = outer.snd := by
  obtain ⟨U,c,hD,hs,ht,_⟩ := D.boundary_disk_boundary hsimple hinner
  exact ⟨U,c,hD,hs,ht⟩

end ChordSectorData
end JSP512Probe.RotationSystem
