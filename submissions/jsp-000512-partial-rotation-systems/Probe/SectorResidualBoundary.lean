import Probe.ChordNeighborAssembly

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [DecidableEq V] in
/-- Every deleted outer-region dart is either an old boundary dart or belongs
to one of the two concrete sector paths. -/
theorem outer_region_path_cover (outer : G.Dart)
    (hinner : ∀ x, ¬R.face.SameCycle outer x → R.face (R.face (R.face x)) = x)
    (n m : ℕ) (d : Fin (n+1) → G.Dart) (e : Fin (m+1) → G.Dart)
    (hd : ∀ i, (d i).fst = outer.snd) (he : ∀ j, (e j).fst = outer.snd)
    (htd : ∀ i, R.face (R.face (R.face (d i).symm)) = (d i).symm)
    (hte : ∀ j, R.face (R.face (R.face (e j).symm)) = (e j).symm)
    (hds : ∀ i : Fin n, R.rotate (d i.succ) = d i.castSucc)
    (hes : ∀ j : Fin m, R.rotate (e j.succ) = e j.castSucc)
    (hstop : R.rotate outer.symm = d (Fin.last n))
    (he0 : R.rotate (e 0) = outer.symm) (hd0 : R.rotate (d 0) = e (Fin.last m))
    (z : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hz : R.outerDeletionRegion outer z) :
    R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val ∨
      (∃ i, z = R.sectorDeletedDart outer.snd (d i) (hd i) (htd i)) ∨
      (∃ j, z = R.sectorDeletedDart outer.snd (e j) (he j) (hte j)) := by
  by_cases ho : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val
  · exact Or.inl ho
  obtain ⟨a,ha,ht,hn,haz⟩ := R.outer_region_sector outer hinner z ho (hz.resolve_left ho)
  have hc := (R.sector_paths_cover outer.snd outer.symm rfl n m d e hd he hds hes
    hstop he0 hd0 a).mp ha
  rcases hc with h | ⟨i,h⟩ | ⟨j,h⟩
  · subst a
    exact False.elim (hn (by simpa using (Equiv.Perm.SameCycle.rfl : R.face.SameCycle outer outer)))
  · subst a
    exact Or.inr (Or.inl ⟨i,haz.symm⟩)
  · subst a
    exact Or.inr (Or.inr ⟨j,haz.symm⟩)

/-- Within a specified split component, removing its sector path leaves only
old boundary darts: sectors from the other component cannot occur there. -/
theorem split_residual_old_boundary (outer : G.Dart)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart) (hxy : x.fst = y.fst)
    (hne : x ≠ y) (hc : (VertexDeletedGraph (G := G) outer.snd).Preconnected)
    (hz : (R.deleteVertex outer.snd).HasGenusZero)
    (hf : (R.deleteVertex outer.snd).face.SameCycle x y)
    {I J : Type*} (f : I → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (g : J → (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hcover : ∀ z, R.outerDeletionRegion outer z →
      R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val ∨
        (∃ i, z = f i) ∨ (∃ j, z = g j)) :
    let S := R.deleteVertex outer.snd
    let H := RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)
    let q := RefinedRotation.vertex _ (S.splitRotation x y)
    (∀ i, H.Reachable (q (f i)) (q y)) →
    (∀ j, H.Reachable (q (g j)) (q x)) →
    (∀ z, R.outerDeletionRegion outer z → H.Reachable (q z) (q x) →
      (∀ j, z ≠ g j) → R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val) ∧
    (∀ z, R.outerDeletionRegion outer z → H.Reachable (q z) (q y) →
      (∀ i, z ≠ f i) → R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val) := by
  dsimp only
  intro hfr hgr
  have hsep := (R.deleteVertex outer.snd).split_copies_not_reachable x y hxy hne hc hz hf
  constructor
  · intro z hr hrx hn
    rcases hcover z hr with ho | ⟨i,rfl⟩ | ⟨j,rfl⟩
    · exact ho
    · exact False.elim (hsep (hrx.symm.trans (hfr i)))
    · exact False.elim (hn j rfl)
  · intro z hr hry hn
    rcases hcover z hr with ho | ⟨i,rfl⟩ | ⟨j,rfl⟩
    · exact ho
    · exact False.elim (hn i rfl)
    · exact False.elim (hsep ((hgr j).symm.trans hry))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Surviving old boundary darts retain source simplicity even when the whole
deleted outer boundary has repeated vertices. -/
theorem old_boundary_survivors_simple (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (hy : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) y).val)
    (hxy : x.fst = y.fst) : x = y := by
  apply (vertexDeletedDartEquiv outer.snd).injective
  apply Subtype.ext
  exact hsimple _ _ hx hy (congrArg Subtype.val hxy)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The old predecessor of the deleted vertex has no surviving old boundary
occurrence; its unique outgoing boundary dart was deleted. -/
theorem old_boundary_avoids_attachment (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (z : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hz : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val) :
    z.fst.val ≠ outer.fst := by
  intro he
  have hh := hsimple _ outer hz Equiv.Perm.SameCycle.rfl he
  exact ((vertexDeletedDartEquiv outer.snd) z).property.2
    (congrArg (fun a : G.Dart => a.snd) hh)

/-- On the exposed-sector component, an old boundary dart cannot have the
chord endpoint as source: the unique such old dart belongs to the other cut. -/
theorem old_boundary_avoids_other_cut (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart) (hxy : x.fst = y.fst)
    (hne : x ≠ y) (hc : (VertexDeletedGraph (G := G) outer.snd).Preconnected)
    (hz : (R.deleteVertex outer.snd).HasGenusZero)
    (hf : (R.deleteVertex outer.snd).face.SameCycle x y)
    (hx : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (z : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (ho : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) z).val) :
    let S := R.deleteVertex outer.snd
    let H := RefinedRotation.graph _ (S.splitRotation x y) (S.split_source x y hxy)
    let q := RefinedRotation.vertex _ (S.splitRotation x y)
    H.Reachable (q z) (q y) → z.fst ≠ y.fst := by
  dsimp only
  intro hr he
  have hzx : z = x := R.old_boundary_survivors_simple outer hsimple z x ho hx
    (he.trans hxy.symm)
  subst z
  exact (R.deleteVertex outer.snd).split_copies_not_reachable x y hxy hne hc hz hf hr

end JSP512Probe.RotationSystem
