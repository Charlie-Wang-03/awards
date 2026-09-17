import Probe.ChordExposesCut
import Probe.ComplementarySectorInterval
import Probe.DiskInstance

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Coherent cuts and both sector intervals generated from one boundary chord.
All later side constructions can use these same witnesses. -/
structure ChordSectorData (outer : G.Dart) (w : V) where
  x : (VertexDeletedGraph (G := G) outer.snd).Dart
  y : (VertexDeletedGraph (G := G) outer.snd).Dart
  cut_source : x.fst = y.fst
  cut_ne : x ≠ y
  chord_vertex : x.fst.val = w
  cut_face : (R.deleteVertex outer.snd).face.SameCycle x y
  old_cut : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val
  region : ∀ z, (R.deleteVertex outer.snd).face.SameCycle x z ↔ R.outerDeletionRegion outer z
  connected : (VertexDeletedGraph (G := G) outer.snd).Connected
  zero : (R.deleteVertex outer.snd).HasGenusZero
  inner : ∀ z, ¬(R.deleteVertex outer.snd).face.SameCycle x z →
    (R.deleteVertex outer.snd).face ((R.deleteVertex outer.snd).face
      ((R.deleteVertex outer.snd).face z)) = z
  n : ℕ
  m : ℕ
  d : Fin (n+1) → G.Dart
  e : Fin (m+1) → G.Dart
  d_source : ∀ i, (d i).fst = outer.snd
  e_source : ∀ j, (e j).fst = outer.snd
  d_triangle : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm
  e_triangle : ∀ j, R.face (R.face (R.face (e j).symm)) = (e j).symm
  d_step : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc
  e_step : ∀ j : Fin m, R.rotate (e j.succ) = e j.castSucc
  d_injective : Function.Injective d
  e_injective : Function.Injective e
  d_avoid : ∀ i, d i ≠ outer.symm
  e_avoid : ∀ j, e j ≠ outer.symm ∧ e j ≠ d 0
  d_end : R.rotate outer.symm = d (Fin.last n)
  e_start : R.rotate (e 0) = outer.symm
  e_end : R.rotate (d 0) = e (Fin.last m)
  sector_cut : y = R.sectorDeletedDart outer.snd (d 0) (d_source 0) (d_triangle 0)

/-- A genuine chord in a triangulated disk supplies all common cut and
interval data simultaneously; no sector witnesses are assumed. -/
theorem chord_sector_data (outer : G.Dart) (hD : R.IsTriangulatedDisk outer)
    (hcorner : R.face outer ≠ outer.symm)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    Nonempty (R.ChordSectorData outer a.fst) := by
  classical
  obtain ⟨r,hr⟩ := R.outer_region_single_orbit outer hD.simple hD.inner hcorner
  obtain ⟨x,y,hx,hy,hne,hxy,hw,hxo,_,s,hs,ht,hsne,hsrot,hys⟩ :=
    R.chord_exposes_sector_vertex outer hD.simple hD.inner r hr a ha hadj hleft hright
  obtain ⟨n,d,hd0,hd,hdt,hdstep,hdinj,hdavoid,hdend⟩ :=
    R.outer_source_sector_interval outer hD.simple hD.inner s hs hsne
  obtain ⟨m,e,he0,he,het,hestep,heinj,heavoid,heend⟩ :=
    R.complementary_sector_interval outer.snd s outer.symm hs rfl hsne hsrot
      (fun z hz hn => R.outer_face_fan outer hD.simple hD.inner z hz hn)
  have hreg : ∀ z, (R.deleteVertex outer.snd).face.SameCycle x z ↔ R.outerDeletionRegion outer z := by
    intro z
    constructor
    · intro hz
      exact (hr z).mp (hx.trans hz)
    · intro hz
      exact hx.symm.trans ((hr z).mpr hz)
  refine ⟨{
    x := x, y := y, cut_source := hxy, cut_ne := hne, chord_vertex := hw
    cut_face := hx.symm.trans hy, old_cut := hxo, region := hreg
    connected := R.outer_vertex_deleted_connected outer hD.connected.preconnected hD.simple hD.inner
    zero := R.boundary_deleteVertex_genusZero outer hD.zero hD.connected.preconnected
      hD.simple hD.inner hcorner
    inner := fun z hz => R.outside_outer_region_triangular outer hD.inner z
      (fun hh => hz ((hreg z).mpr hh))
    n := n, m := m, d := d, e := e
    d_source := hd, e_source := he, d_triangle := hdt, e_triangle := het
    d_step := hdstep, e_step := hestep, d_injective := hdinj, e_injective := heinj
    d_avoid := hdavoid, e_avoid := ?_, d_end := hdend, e_start := he0, e_end := ?_
    sector_cut := ?_ }⟩
  · intro j
    exact ⟨(heavoid j).1,by rw [hd0]; exact (heavoid j).2⟩
  · rw [hd0]
    exact heend
  · subst s
    exact hys

end JSP512Probe.RotationSystem
