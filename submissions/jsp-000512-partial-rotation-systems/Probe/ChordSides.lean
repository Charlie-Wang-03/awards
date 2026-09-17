import Probe.ChordSectorData
import Probe.ComplementarySectorSide

namespace JSP512Probe.RotationSystem.ChordSectorData
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {R : RotationSystem G}
  {outer : G.Dart} {w : V}

def firstPath (D : R.ChordSectorData outer w) (i : Fin (D.n+1)) :=
  R.sectorDeletedDart outer.snd (D.d i) (D.d_source i) (D.d_triangle i)

def secondPath (D : R.ChordSectorData outer w) (j : Fin (D.m+1)) :=
  R.sectorDeletedDart outer.snd (D.e j) (D.e_source j) (D.e_triangle j)

def exposedSide (D : R.ChordSectorData outer w) : Set {u : V // u ≠ outer.snd} :=
  (R.deleteVertex outer.snd).splitSide D.x (D.firstPath 0)
    (D.cut_source.trans (congrArg (fun z => z.fst) D.sector_cut)) (D.firstPath 0)

def boundarySide (D : R.ChordSectorData outer w) : Set {u : V // u ≠ outer.snd} :=
  (R.deleteVertex outer.snd).splitSide D.x (D.firstPath 0)
    (D.cut_source.trans (congrArg (fun z => z.fst) D.sector_cut)) D.x

/-- The coherent intervals themselves certify that the chord endpoint differs
from the deleted vertex's old predecessor. -/
theorem chord_ne_predecessor (D : R.ChordSectorData outer w) : w ≠ outer.fst := by
  intro hw
  have hs : (R.rotate (D.d 0)).snd = w := by
    have hh := congrArg (fun z : (VertexDeletedGraph (G := G) outer.snd).Dart => z.fst.val)
      D.sector_cut
    change D.y.fst.val = (R.face (R.rotate (D.d 0))).fst at hh
    rw [R.face_source] at hh
    exact hh.symm.trans ((congrArg Subtype.val D.cut_source).symm.trans D.chord_vertex)
  have hr : R.rotate (D.d 0) = outer.symm := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact (R.source _).trans (D.d_source 0)
    · exact hs.trans hw
  have he := R.rotate.injective (D.e_start.trans hr.symm)
  exact (D.e_avoid 0).2 he

/-- The old predecessor lies on the old-boundary side and not on the exposed
side. It is therefore never a missing exceptional boundary case there. -/
theorem predecessor_side (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b) :
    ∃ u : {u : V // u ≠ outer.snd}, u.val = outer.fst ∧
      u ∈ D.boundarySide ∧ u ∉ D.exposedSide := by
  let S := R.deleteVertex outer.snd
  let f := D.firstPath
  let g := D.secondPath
  have hxy : D.x.fst = (f 0).fst := D.cut_source.trans (congrArg (fun z => z.fst) D.sector_cut)
  have hne : D.x ≠ f 0 := by simpa only [D.sector_cut,f,firstPath] using D.cut_ne
  have hf : S.face.SameCycle D.x (f 0) := by
    simpa only [D.sector_cut,f,firstPath,S] using D.cut_face
  have hgr := R.complementary_sector_side outer hsimple D.x D.old_cut (D.d 0)
    (D.d_source 0) (D.d_triangle 0) D.m D.e D.e_source D.e_triangle
    (fun j => (D.e_avoid j).1) (fun j => (D.e_avoid j).2) D.e_step D.e_end hxy
  have hsource : (g 0).fst.val = outer.fst := by
    change (R.face (R.rotate (D.e 0))).fst = outer.fst
    rw [R.face_source,D.e_start]
    rfl
  have hm : (g 0).fst ∈ D.boundarySide := ⟨g 0,rfl,hgr 0⟩
  refine ⟨(g 0).fst,hsource,hm,?_⟩
  intro hb
  have he := (S.split_sides_inter D.x (f 0) hxy hne D.connected.preconnected D.zero hf _).mp ⟨hm,hb⟩
  exact D.chord_ne_predecessor
    (D.chord_vertex.symm.trans ((congrArg Subtype.val he).symm.trans hsource))

/-- Consequently every vertex of the exposed survivor side avoids the old
predecessor, without an extra hypothesis on an individual vertex. -/
theorem exposed_avoids_predecessor (D : R.ChordSectorData outer w)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b) (u : D.exposedSide) : u.val.val ≠ outer.fst := by
  obtain ⟨v,hv,_,hn⟩ := D.predecessor_side hsimple
  intro hu
  have he : u.val = v := Subtype.ext (hu.trans hv.symm)
  exact hn (he ▸ u.property)

end JSP512Probe.RotationSystem.ChordSectorData
