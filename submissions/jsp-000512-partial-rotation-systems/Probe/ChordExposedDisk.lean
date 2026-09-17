import Probe.ChordSides
import Probe.OldBoundarySideResidual
import Probe.ExposedSideDisk
import Probe.RestoredRouteIso

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {R : RotationSystem G}
  {outer : G.Dart} {w : V}

namespace ChordSectorData

/-- Coherent chord data constructs a disk on the original restored induced
side, with the chord itself as the distinguished outer edge. -/
theorem exposed_disk_boundary (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a) :
    letI : Fintype (restoreSide outer.snd D.exposedSide) := Fintype.ofFinite _
    ∃ U : RotationSystem (G.induce (restoreSide outer.snd D.exposedSide)),
      ∃ c, U.IsTriangulatedDisk c ∧ c.fst.val = w ∧ c.snd.val = outer.snd ∧
        ∀ u, u.val ∈ R.facialVertices outer → u ∈ U.facialVertices c := by
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
  have htarget : Function.Injective (fun i => (f i).snd) := by
    intro i j he
    exact D.d_injective (R.sector_target_injective outer.snd _ _ _ _ _ _ he)
  have havoid := R.sector_interval_source_avoidance outer.snd D.n D.d D.d_source D.d_triangle
    D.d_step D.d_injective outer.symm D.d_end (D.d_avoid 0).symm
  have hcover := R.outer_region_path_cover outer hinner D.n D.m D.d D.e D.d_source D.e_source
    D.d_triangle D.e_triangle D.d_step D.e_step D.d_end D.e_start D.e_end
  let A := S.splitSide D.x (f 0) hxy (f 0)
  let : Fintype A := Fintype.ofFinite _
  let : Fintype (restoreSide outer.snd A) := Fintype.ofFinite _
  let T := S.splitSideRotation D.x (f 0) hxy hne D.connected.preconnected D.zero hf (f 0)
  let p := fun i => S.splitSideDart D.x (f 0) hxy (f 0) (f i) (hfr i)
  obtain ⟨K,hold,hcenter,U,c,hc,hD,hverts⟩ := R.exposed_side_disk outer hsimple
    D.x (f 0) hxy hne D.connected.preconnected D.zero hf D.old_cut
    (fun z hz => (D.region z).mp hz) D.n (D.m+1) f g rfl hstep
    (fun i => hcuts.1 i.succ) hcuts.2 htarget havoid D.inner hcover hfr hgr
  have hneighbors := (R.chord_sector_neighbors outer hsimple D.x D.old_cut D.n D.m D.d D.e
    D.d_source D.e_source D.d_triangle D.e_triangle D.d_avoid (fun j => (D.e_avoid j).1)
    (fun j => (D.e_avoid j).2) D.d_injective D.d_step D.e_step D.d_end D.e_start D.e_end
    hxy D.connected.preconnected D.zero hf).2
  let E := restoredRouteIso G outer.snd A T (p 0) (D.n+1) p K hold hcenter
    (fun u => hneighbors u.val u.property)
  refine ⟨U.mapIso E,isoDarts E c.symm,U.mapIso_disk E c.symm hD,?_,?_,?_⟩
  · have ha : ((T.face.symm (p 0)).symm.fst).val.val = w := by
      change (T.face.symm (p 0)).snd.val.val = w
      rw [T.face_inverse_target]
      exact (congrArg Subtype.val hxy).symm.trans D.chord_vertex
    change (E c.snd).val = w
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
      by_cases he : u.val = (f 0).fst
      · right; left
        apply congrArg some
        rw [ha]
        exact Subtype.ext he
      · right; right
        refine ⟨u,rfl,?_⟩
        have hcut : u.val ≠ D.x.fst := by rw [hxy]; exact he
        exact R.old_boundary_side_residual outer hsimple D.x (f 0) hxy hne
          D.connected.preconnected D.zero hf (fun z hz => (D.region z).mpr hz)
          (f 0) (f 0) hf (D.n+1) f
          (fun i => R.deleted_sector_not_old_outer outer hsimple _ (D.d_source i)
            (D.d_avoid i) (D.d_triangle i))
          (hfr 0) hfr u.val u.property hu (D.exposed_avoids_predecessor hsimple u) hcut

/-- Compatibility projection of the boundary-preserving disk construction. -/
theorem exposed_disk (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a) :
    letI : Fintype (restoreSide outer.snd D.exposedSide) := Fintype.ofFinite _
    ∃ U : RotationSystem (G.induce (restoreSide outer.snd D.exposedSide)),
      ∃ c, U.IsTriangulatedDisk c ∧ c.fst.val = w ∧ c.snd.val = outer.snd := by
  obtain ⟨U,c,hD,hs,ht,_⟩ := D.exposed_disk_boundary hsimple hinner
  exact ⟨U,c,hD,hs,ht⟩

end ChordSectorData
end JSP512Probe.RotationSystem
