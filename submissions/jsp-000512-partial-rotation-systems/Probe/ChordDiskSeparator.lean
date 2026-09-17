import Probe.ChordBoundaryDisk

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {R : RotationSystem G}
  {outer : G.Dart} {w : V}

/-- The very same restored sides used for the two disk constructions cover
all vertices and edges, intersect exactly at the chord, and are smaller. -/
theorem ChordSectorData.separator (D : R.ChordSectorData outer w) :
    let A := restoreSide outer.snd D.boundarySide
    let B := restoreSide outer.snd D.exposedSide
    (∀ u, u ∈ A ∨ u ∈ B) ∧
    (∀ u z, G.Adj u z → (u ∈ A ∧ z ∈ A) ∨ (u ∈ B ∧ z ∈ B)) ∧
    (∀ u, (u ∈ A ∧ u ∈ B) ↔ u = outer.snd ∨ u = w) ∧
    Nat.card A < Fintype.card V ∧ Nat.card B < Fintype.card V := by
  classical
  let S := R.deleteVertex outer.snd
  let y := D.firstPath 0
  have hxy : D.x.fst = y.fst := D.cut_source.trans (congrArg (fun z => z.fst) D.sector_cut)
  have hne : D.x ≠ y := by simpa only [D.sector_cut, y, ChordSectorData.firstPath] using D.cut_ne
  have hf : S.face.SameCycle D.x y := by
    simpa only [D.sector_cut, y, ChordSectorData.firstPath, S] using D.cut_face
  have hp := S.split_sides_proper D.x y hxy hne D.connected.preconnected D.zero hf
  have result := restore_separator (G := G) outer.snd D.boundarySide D.exposedSide D.x.fst
    (S.split_sides_cover D.x y hxy hne D.connected.preconnected)
    (S.split_sides_edges D.x y hxy hne D.connected.preconnected)
    (S.split_sides_inter D.x y hxy hne D.connected.preconnected D.zero hf)
    ⟨y.snd,hp.2.2⟩ ⟨D.x.snd,hp.1.2⟩
  simpa only [D.chord_vertex] using result

/-- A genuine boundary chord yields two strictly smaller induced triangulated
disks on a common edge-covering separator. The first keeps the original
specified outer edge; the second uses the chord as its specified outer edge. -/
theorem chord_disk_separator_boundary_edges (R : RotationSystem G) (outer : G.Dart)
    (hD : R.IsTriangulatedDisk outer) (hcorner : R.face outer ≠ outer.symm)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    ∃ A B : Set V,
      (∀ u, u ∈ A ∨ u ∈ B) ∧
      (∀ u z, G.Adj u z → (u ∈ A ∧ z ∈ A) ∨ (u ∈ B ∧ z ∈ B)) ∧
      (∀ u, (u ∈ A ∧ u ∈ B) ↔ u = outer.snd ∨ u = a.fst) ∧
      Nat.card A < Fintype.card V ∧ Nat.card B < Fintype.card V ∧
      (letI : Fintype A := Fintype.ofFinite _
       ∃ U : RotationSystem (G.induce A), ∃ c,
         U.IsTriangulatedDisk c ∧ c.fst.val = outer.fst ∧ c.snd.val = outer.snd ∧
         (∀ u, u.val ∈ R.facialVertices outer → u ∈ U.facialVertices c) ∧
         ∀ pre : G.Dart, R.face.SameCycle outer pre → pre.snd = outer.fst →
           pre.fst ≠ outer.snd → ∃ e, U.face.SameCycle c e ∧
             e.fst.val = pre.fst ∧ e.snd.val = pre.snd) ∧
      (letI : Fintype B := Fintype.ofFinite _
       ∃ U : RotationSystem (G.induce B), ∃ c,
         U.IsTriangulatedDisk c ∧ c.fst.val = a.fst ∧ c.snd.val = outer.snd ∧
         ∀ u, u.val ∈ R.facialVertices outer → u ∈ U.facialVertices c) := by
  obtain ⟨D⟩ := R.chord_sector_data outer hD hcorner a ha hadj hleft hright
  obtain ⟨hcover,hedges,hinter,hA,hB⟩ := D.separator
  exact ⟨restoreSide outer.snd D.boundarySide,restoreSide outer.snd D.exposedSide,
    hcover,hedges,hinter,hA,hB,D.boundary_disk_boundary_edges hD.simple hD.inner,D.exposed_disk_boundary hD.simple hD.inner⟩

/-- Compatibility projection retaining inherited boundary vertices. -/
theorem chord_disk_separator_boundary (R : RotationSystem G) (outer : G.Dart)
    (hD : R.IsTriangulatedDisk outer) (hcorner : R.face outer ≠ outer.symm)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    ∃ A B : Set V,
      (∀ u, u ∈ A ∨ u ∈ B) ∧
      (∀ u z, G.Adj u z → (u ∈ A ∧ z ∈ A) ∨ (u ∈ B ∧ z ∈ B)) ∧
      (∀ u, (u ∈ A ∧ u ∈ B) ↔ u = outer.snd ∨ u = a.fst) ∧
      Nat.card A < Fintype.card V ∧ Nat.card B < Fintype.card V ∧
      (letI : Fintype A := Fintype.ofFinite _
       ∃ U : RotationSystem (G.induce A), ∃ c,
         U.IsTriangulatedDisk c ∧ c.fst.val = outer.fst ∧ c.snd.val = outer.snd ∧
         ∀ u, u.val ∈ R.facialVertices outer → u ∈ U.facialVertices c) ∧
      (letI : Fintype B := Fintype.ofFinite _
       ∃ U : RotationSystem (G.induce B), ∃ c,
         U.IsTriangulatedDisk c ∧ c.fst.val = a.fst ∧ c.snd.val = outer.snd ∧
         ∀ u, u.val ∈ R.facialVertices outer → u ∈ U.facialVertices c) := by
  obtain ⟨A,B,hcov,hedges,hinter,hA,hB,hdA,hdB⟩ :=
    R.chord_disk_separator_boundary_edges outer hD hcorner a ha hadj hleft hright
  refine ⟨A,B,hcov,hedges,hinter,hA,hB,?_,hdB⟩
  obtain ⟨U,c,hD,hs,ht,hb,_⟩ := hdA
  exact ⟨U,c,hD,hs,ht,hb⟩

/-- Compatibility projection of the boundary-preserving chord separator. -/
theorem chord_disk_separator (R : RotationSystem G) (outer : G.Dart)
    (hD : R.IsTriangulatedDisk outer) (hcorner : R.face outer ≠ outer.symm)
    (a : G.Dart) (ha : R.face.SameCycle outer a) (hadj : G.Adj outer.snd a.fst)
    (hleft : a.fst ≠ outer.fst) (hright : a.fst ≠ (R.face outer).snd) :
    ∃ A B : Set V,
      (∀ u, u ∈ A ∨ u ∈ B) ∧
      (∀ u z, G.Adj u z → (u ∈ A ∧ z ∈ A) ∨ (u ∈ B ∧ z ∈ B)) ∧
      (∀ u, (u ∈ A ∧ u ∈ B) ↔ u = outer.snd ∨ u = a.fst) ∧
      Nat.card A < Fintype.card V ∧ Nat.card B < Fintype.card V ∧
      (letI : Fintype A := Fintype.ofFinite _
       ∃ U : RotationSystem (G.induce A), ∃ c,
         U.IsTriangulatedDisk c ∧ c.fst.val = outer.fst ∧ c.snd.val = outer.snd) ∧
      (letI : Fintype B := Fintype.ofFinite _
       ∃ U : RotationSystem (G.induce B), ∃ c,
         U.IsTriangulatedDisk c ∧ c.fst.val = a.fst ∧ c.snd.val = outer.snd) := by
  obtain ⟨A,B,hcov,hedges,hinter,hA,hB,hdA,hdB⟩ :=
    R.chord_disk_separator_boundary outer hD hcorner a ha hadj hleft hright
  refine ⟨A,B,hcov,hedges,hinter,hA,hB,?_,?_⟩
  · obtain ⟨U,c,hD,hs,ht,_⟩ := hdA
    exact ⟨U,c,hD,hs,ht⟩
  · obtain ⟨U,c,hD,hs,ht,_⟩ := hdB
    exact ⟨U,c,hD,hs,ht⟩

end JSP512Probe.RotationSystem
