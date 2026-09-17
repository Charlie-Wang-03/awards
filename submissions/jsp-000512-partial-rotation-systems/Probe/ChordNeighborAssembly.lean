import Probe.SectorNeighborCoverage

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- The actual two sector paths give exact neighbor sets on both induced
split sides. Candidate membership, global coverage and shared-endpoint
identification are all derived from the paths and their endpoint equations. -/
theorem chord_sector_neighbors (outer : G.Dart)
    (hsimple : ∀ x y, R.face.SameCycle outer x → R.face.SameCycle outer y →
      x.fst = y.fst → x = y)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (n m : ℕ) (d : Fin (n+1) → G.Dart) (e : Fin (m+1) → G.Dart)
    (hd : ∀ i, (d i).fst = outer.snd) (he : ∀ j, (e j).fst = outer.snd)
    (htd : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (hte : ∀ j, R.face (R.face (R.face (e j).symm)) = (e j).symm)
    (had : ∀ i, d i ≠ outer.symm) (hae : ∀ j, e j ≠ outer.symm)
    (hbe : ∀ j, e j ≠ d 0) (hinj : Function.Injective d)
    (hds : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hes : ∀ j : Fin m, R.rotate (e j.succ) = e j.castSucc)
    (hstop : R.rotate outer.symm = d (Fin.last n))
    (he0 : R.rotate (e 0) = outer.symm) (hd0 : R.rotate (d 0) = e (Fin.last m)) :
    let H := VertexDeletedGraph (G := G) outer.snd
    let S := R.deleteVertex outer.snd
    let f := fun i => R.sectorDeletedDart outer.snd (d i) (hd i) (htd i)
    let g := fun j => R.sectorDeletedDart outer.snd (e j) (he j) (hte j)
    ∀ (hxy : x.fst = (f 0).fst) (_hc : H.Preconnected) (_hz : S.HasGenusZero)
      (_hf : S.face.SameCycle x (f 0)),
      (∀ u ∈ S.splitSide x (f 0) hxy x,
        G.Adj outer.snd u.val ↔ u = (g 0).fst ∨ ∃ j, u = (g j).snd) ∧
      (∀ u ∈ S.splitSide x (f 0) hxy (f 0),
        G.Adj outer.snd u.val ↔ u = (f 0).fst ∨ ∃ i, u = (f i).snd) := by
  classical
  dsimp only
  intro hxy hc hz hf
  let S := R.deleteVertex outer.snd
  let f := fun i => R.sectorDeletedDart outer.snd (d i) (hd i) (htd i)
  let g := fun j => R.sectorDeletedDart outer.snd (e j) (he j) (hte j)
  have hcut := R.chord_sector_cut_avoidance outer hsimple x hx n d hd htd had hinj
  have hfr := S.split_path_in_component x (f 0) hxy (f 0) n f
    SimpleGraph.Reachable.rfl
    (fun i => R.sector_predecessor_step outer.snd _ _ _ _ (hds i) _ _)
    (fun i => hcut.1 i.succ) hcut.2
  have hgr := R.complementary_sector_side outer hsimple x hx (d 0) (hd 0) (htd 0)
    m e he hte hae hbe hes hd0 hxy
  have hft : ∀ i, (f i).snd.val = (d i).snd := by
    intro i
    exact (R.sector_endpoints_of_closed (d i) (htd i)).2
  have hgt : ∀ j, (g j).snd.val = (e j).snd := by
    intro j
    exact (R.sector_endpoints_of_closed (e j) (hte j)).2
  have hg0 : (g 0).fst.val = outer.fst := by
    change (R.face (R.rotate (e 0))).fst = outer.fst
    rw [R.face_source, he0]
    rfl
  have hshared : x.fst = (g (Fin.last m)).snd := by
    rw [hxy]
    apply Subtype.ext
    change (R.face (R.rotate (d 0))).fst = (g (Fin.last m)).snd.val
    rw [R.face_source, hd0, hgt]
  have hcov : ∀ u : {u : V // u ≠ outer.snd}, G.Adj outer.snd u.val ↔
      u = (g 0).fst ∨ (∃ i, u = (f i).snd) ∨ (∃ j, u = (g j).snd) := by
    intro u
    have hh := R.sector_paths_neighbors outer.snd outer.symm rfl n m d e hd he hds hes
      hstop he0 hd0 u.val
    constructor
    · intro hu
      rcases hh.mp hu with hu | ⟨i,hu⟩ | ⟨j,hu⟩
      · exact Or.inl (Subtype.ext (hu.trans hg0.symm))
      · exact Or.inr (Or.inl ⟨i,Subtype.ext (hu.trans (hft i).symm)⟩)
      · exact Or.inr (Or.inr ⟨j,Subtype.ext (hu.trans (hgt j).symm)⟩)
    · rintro (rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩)
      · exact hh.mpr (Or.inl hg0)
      · exact hh.mpr (Or.inr (Or.inl ⟨i,hft i⟩))
      · exact hh.mpr (Or.inr (Or.inr ⟨j,hgt j⟩))
  have ha := (S.splitSideDart x (f 0) hxy x (g 0) (hgr 0)).fst.property
  have hb := fun i => (S.splitSideDart x (f 0) hxy (f 0) (f i) (hfr i)).snd.property
  have hg := fun j => (S.splitSideDart x (f 0) hxy x (g j) (hgr j)).snd.property
  have hh := R.split_side_neighbor_coverage outer.snd x (f 0) hxy (hcut.1 0).symm hc hz hf
    (fun i => (f i).snd) (fun j => (g j).snd) (g 0).fst hcov ha hb hg
    ⟨Fin.last m,hshared⟩
  rw [hxy] at hh
  exact hh

end JSP512Probe.RotationSystem
