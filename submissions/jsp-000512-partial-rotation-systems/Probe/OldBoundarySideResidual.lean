import Probe.SideBoundaryInheritance

namespace JSP512Probe.RotationSystem
open EdgeInsertion
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- An original boundary vertex in a split side remains on its retained
boundary, except for the deleted predecessor and the split endpoint, which
are handled by the distinguished attachments. -/
theorem old_boundary_side_residual (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart) (hxy : x.fst = y.fst)
    (hne : x ≠ y) (hc : (VertexDeletedGraph (G := G) outer.snd).Preconnected)
    (hz : (R.deleteVertex outer.snd).HasGenusZero)
    (hf : (R.deleteVertex outer.snd).face.SameCycle x y)
    (hregion : ∀ z, R.outerDeletionRegion outer z →
      (R.deleteVertex outer.snd).face.SameCycle x z)
    (mark root : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hroot : (R.deleteVertex outer.snd).face.SameCycle x root)
    (n : ℕ) (p : Fin n → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hpath : ∀ i, ¬R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) (p i)).val) :
    let S := R.deleteVertex outer.snd
    let H := RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)
    let q := RefinedRotation.vertex _ (S.splitRotation x y)
    ∀ (hr : H.Reachable (q root) (q mark)) (hp : ∀ i, H.Reachable (q (p i)) (q mark))
      (u : {u : V // u ≠ outer.snd}) (hmem : u ∈ S.splitSide x y hxy mark),
      u.val ∈ R.facialVertices outer → u.val ≠ outer.fst → u ≠ x.fst →
      let T := S.splitSideRotation x y hxy hne hc hz hf mark
      let r := S.splitSideDart x y hxy mark root hr
      let ds := List.ofFn (fun i => S.splitSideDart x y hxy mark (p i) (hp i))
      ResidualBoundaryVertex ((VertexDeletedGraph (G := G) outer.snd).induce
        (S.splitSide x y hxy mark)) T (T.face.symm r).symm ds ⟨u,hmem⟩ := by
  dsimp only
  intro hr hp u hmem hu hleft hcut
  let S := R.deleteVertex outer.snd
  obtain ⟨d,hdo,hdu⟩ := R.old_boundary_surviving_dart outer hsimple u.val hu u.property hleft
  have hsource : d.fst = u := Subtype.ext hdu
  have haway : d.fst ≠ x.fst := by rw [hsource]; exact hcut
  have hmember : d.fst ∈ S.splitSide x y hxy mark := hsource ▸ hmem
  have hd := S.splitSide_source_membership x y hxy hne mark d haway hmember
  have ho := hregion d (Or.inl hdo)
  have hn : ∀ i, d ≠ p i := by
    intro i he
    exact hpath i (he ▸ hdo)
  have hv := S.splitSideDart_residual_vertex x y hxy hne hc hz hf mark root d hr hd
    hroot ho n p hp hn
  dsimp only at hv
  have he : (S.splitSideDart x y hxy mark d hd).fst = ⟨u,hmem⟩ := Subtype.ext hsource
  rw [he] at hv
  exact hv

/-- The old cut occurrence itself survives the complementary restoration
path, retaining the chord endpoint on the old-boundary side. -/
theorem old_cut_side_residual (outer : G.Dart)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart) (hxy : x.fst = y.fst)
    (hne : x ≠ y) (hc : (VertexDeletedGraph (G := G) outer.snd).Preconnected)
    (hz : (R.deleteVertex outer.snd).HasGenusZero)
    (hf : (R.deleteVertex outer.snd).face.SameCycle x y)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (root : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hroot : (R.deleteVertex outer.snd).face.SameCycle x root)
    (n : ℕ) (p : Fin n → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hpath : ∀ i, ¬R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) (p i)).val) :
    let S := R.deleteVertex outer.snd
    let H := RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)
    let q := RefinedRotation.vertex _ (S.splitRotation x y)
    ∀ (hr : H.Reachable (q root) (q x)) (hp : ∀ i, H.Reachable (q (p i)) (q x)),
      let T := S.splitSideRotation x y hxy hne hc hz hf x
      let r := S.splitSideDart x y hxy x root hr
      let z := S.splitSideDart x y hxy x x SimpleGraph.Reachable.rfl
      let ds := List.ofFn (fun i => S.splitSideDart x y hxy x (p i) (hp i))
      ResidualBoundaryVertex ((VertexDeletedGraph (G := G) outer.snd).induce
        (S.splitSide x y hxy x)) T (T.face.symm r).symm ds z.fst := by
  dsimp only
  intro hr hp
  apply (R.deleteVertex outer.snd).splitSideDart_residual_vertex x y hxy hne hc hz hf
    x root x hr SimpleGraph.Reachable.rfl hroot Equiv.Perm.SameCycle.rfl n p hp
  intro i he
  exact hpath i (he ▸ hx)

end JSP512Probe.RotationSystem
