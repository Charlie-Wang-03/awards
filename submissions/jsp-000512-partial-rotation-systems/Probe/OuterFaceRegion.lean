import Probe.OuterFaceFan

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

/-- Surviving old outer darts and opposite sides of sectors incident to the
removed boundary vertex. This definition does not assume a single new orbit. -/
def outerDeletionRegion (outer : G.Dart)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart) : Prop :=
  R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val ∨
    (R.face ((vertexDeletedDartEquiv outer.snd) x).val).snd = outer.snd

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every newly exposed dart is exactly the surviving side of an inner sector. -/
theorem outer_region_sector (outer : G.Dart)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : ¬R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val)
    (hv : (R.face ((vertexDeletedDartEquiv outer.snd) x).val).snd = outer.snd) :
    ∃ (d : G.Dart) (hd : d.fst = outer.snd)
      (ht : R.face (R.face (R.face d.symm)) = d.symm),
      ¬R.face.SameCycle outer d.symm ∧ R.sectorDeletedDart outer.snd d hd ht = x := by
  let a := ((vertexDeletedDartEquiv outer.snd) x).val
  let d := (R.face a).symm
  have hn : ¬R.face.SameCycle outer d.symm := by
    intro hc
    have hh : R.face.SameCycle outer (R.face a) := by
      simpa only [d, SimpleGraph.Dart.symm_symm] using hc
    exact hx hh.of_apply_right
  refine ⟨d, hv, hinner _ hn, hn, ?_⟩
  apply (vertexDeletedDartEquiv outer.snd).injective
  apply Subtype.ext
  change R.face (R.face (R.face a)) = a
  exact hinner a hx

/-- The candidate outer region is closed under the actual deleted face step. -/
theorem outer_region_step (outer : G.Dart)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.outerDeletionRegion outer x) :
    R.outerDeletionRegion outer ((R.deleteVertex outer.snd).face x) := by
  unfold outerDeletionRegion at hx ⊢
  rw [R.vertex_deleted_face_formula]
  split_ifs with hv
  · let a := ((vertexDeletedDartEquiv outer.snd) x).val
    let b := (R.face a).symm
    have he : R.rotate (R.face a) = R.face b := by
      change R.rotate (R.face a) = R.rotate (R.face a).symm.symm
      rw [SimpleGraph.Dart.symm_symm]
    rw [he]
    by_cases hb : R.face.SameCycle outer b
    · exact Or.inl hb.apply_right
    · right
      have ht := hinner b hb
      have hh := congrArg (fun d : G.Dart => d.fst) ht
      rw [R.face_source] at hh
      exact hh.trans hv
  · exact Or.inl ((hx.resolve_right hv).apply_right)

/-- Region membership is constant on each deleted facial orbit. -/
theorem outer_region_sameCycle (outer : G.Dart)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hxy : (R.deleteVertex outer.snd).face.SameCycle x y)
    (hx : R.outerDeletionRegion outer x) : R.outerDeletionRegion outer y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact R.outer_region_step outer hinner _ ih

/-- Every step outside the candidate outer region agrees with the old face. -/
theorem outside_outer_region_step (outer : G.Dart)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : ¬R.outerDeletionRegion outer x) :
    ((vertexDeletedDartEquiv outer.snd) ((R.deleteVertex outer.snd).face x)).val =
      R.face ((vertexDeletedDartEquiv outer.snd) x).val := by
  rw [R.vertex_deleted_face_formula, ite_eq_right (fun h => hx (Or.inr h))]

/-- All faces outside the candidate outer region retain triangular closure. -/
theorem outside_outer_region_triangular (outer : G.Dart)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (x : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : ¬R.outerDeletionRegion outer x) :
    (R.deleteVertex outer.snd).face ((R.deleteVertex outer.snd).face
      ((R.deleteVertex outer.snd).face x)) = x := by
  let F := (R.deleteVertex outer.snd).face
  have h₁ : ¬R.outerDeletionRegion outer (F x) := fun h =>
    hx (R.outer_region_sameCycle outer hinner _ _ Equiv.Perm.SameCycle.rfl.apply_left h)
  have h₂ : ¬R.outerDeletionRegion outer (F (F x)) := fun h =>
    h₁ (R.outer_region_sameCycle outer hinner _ _ Equiv.Perm.SameCycle.rfl.apply_left h)
  apply (vertexDeletedDartEquiv outer.snd).injective
  apply Subtype.ext
  rw [R.outside_outer_region_step outer (F (F x)) h₂,
    R.outside_outer_region_step outer (F x) h₁, R.outside_outer_region_step outer x hx]
  exact hinner _ (fun h => hx (Or.inl h))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Under the boundary no-chord condition, distinct candidate boundary darts
have distinct source vertices, even across the old-boundary/fan junctions. -/
theorem outer_region_source_injective (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hchord : ∀ a, R.face.SameCycle outer a → G.Adj outer.snd a.fst →
      a.fst = outer.fst ∨ a.fst = (R.face outer).snd)
    (x y : (VertexDeletedGraph (G := G) outer.snd).Dart)
    (hx : R.outerDeletionRegion outer x) (hy : R.outerDeletionRegion outer y)
    (hxy : x.fst = y.fst) : x = y := by
  let lift := fun z : (VertexDeletedGraph (G := G) outer.snd).Dart =>
    ((vertexDeletedDartEquiv outer.snd) z).val
  have src : (lift x).fst = (lift y).fst := congrArg Subtype.val hxy
  have triangle : ∀ a : G.Dart, ¬R.face.SameCycle outer a →
      (R.face (R.face a)).snd = a.fst := by
    intro a ha
    have h := congrArg (fun d : G.Dart => d.fst) (hinner a ha)
    rwa [R.face_source] at h
  have mixed : ∀ a b : G.Dart, R.face.SameCycle outer a →
      ¬R.face.SameCycle outer b → (R.face b).snd = outer.snd →
      a.snd ≠ outer.snd → a.fst = b.fst → False := by
    intro a b ha hb hv hsur hs
    have ht := triangle b hb
    have adj : G.Adj outer.snd a.fst := by
      have hh := (R.face (R.face b)).adj
      rw [R.face_source, hv, ht, ← hs] at hh
      exact hh
    rcases hchord a ha adj with hleft | hright
    · have he := hsimple a outer ha Equiv.Perm.SameCycle.rfl hleft
      exact hsur (congrArg (fun d : G.Dart => d.snd) he)
    · have he : R.face (R.face b) = R.face outer := by
        apply SimpleGraph.Dart.ext
        apply Prod.ext
        · rw [R.face_source, R.face_source, hv]
        · exact ht.trans (hs.symm.trans hright)
      have hh : R.face.SameCycle outer (R.face (R.face b)) := by
        rw [he]
        exact Equiv.Perm.SameCycle.rfl.apply_right
      exact hb hh.of_apply_right.of_apply_right
  have eqold : lift x = lift y := by
    by_cases hxo : R.face.SameCycle outer (lift x)
    · by_cases hyo : R.face.SameCycle outer (lift y)
      · exact hsimple _ _ hxo hyo src
      · exact False.elim (mixed _ _ hxo hyo (hy.resolve_left hyo)
          ((vertexDeletedDartEquiv outer.snd) x).property.2 src)
    · have hxv := hx.resolve_left hxo
      by_cases hyo : R.face.SameCycle outer (lift y)
      · exact False.elim (mixed _ _ hyo hxo hxv
          ((vertexDeletedDartEquiv outer.snd) y).property.2 src.symm)
      · have hyv := hy.resolve_left hyo
        apply R.face.injective
        apply R.face.injective
        apply SimpleGraph.Dart.ext
        apply Prod.ext
        · rw [R.face_source, R.face_source, hxv, hyv]
        · exact (triangle _ hxo).trans (src.trans (triangle _ hyo).symm)
  apply (vertexDeletedDartEquiv outer.snd).injective
  exact Subtype.ext eqold

/-- The candidate region has precisely the surviving old boundary vertices
and all neighbors of the removed vertex. The outer corner is nonbacktracking. -/
theorem outer_region_vertices (outer : G.Dart)
    (hsimple : ∀ a b, R.face.SameCycle outer a → R.face.SameCycle outer b →
      a.fst = b.fst → a = b)
    (hinner : ∀ a, ¬R.face.SameCycle outer a → R.face (R.face (R.face a)) = a)
    (hcorner : R.face outer ≠ outer.symm) (u : V) :
    (∃ x : (VertexDeletedGraph (G := G) outer.snd).Dart,
      R.outerDeletionRegion outer x ∧ x.fst.val = u) ↔
    u ≠ outer.snd ∧ ((∃ a, R.face.SameCycle outer a ∧ a.fst = u) ∨ G.Adj outer.snd u) := by
  have old : ∀ a : G.Dart, R.face.SameCycle outer a → a.fst ≠ outer.snd →
      ∃ x : (VertexDeletedGraph (G := G) outer.snd).Dart,
        R.outerDeletionRegion outer x ∧ x.fst.val = a.fst := by
    intro a ha hv
    by_cases ht : a.snd = outer.snd
    · have he : a = outer := R.face.injective (hsimple _ _ ha.apply_right
        Equiv.Perm.SameCycle.rfl.apply_right (by rw [R.face_source, R.face_source, ht]))
      subst a
      let p := R.face.symm outer
      have hp : R.face.SameCycle outer p := Equiv.Perm.SameCycle.rfl.symm_apply_right
      have hpt : p.snd = outer.fst := R.face_inverse_target outer
      have hps : p.fst ≠ outer.snd := by
        intro h
        have he := hsimple p (R.face outer) hp Equiv.Perm.SameCycle.rfl.apply_right
          (h.trans (R.face_source outer).symm)
        apply hcorner
        apply SimpleGraph.Dart.ext
        exact Prod.ext (R.face_source outer) ((congrArg (fun d : G.Dart => d.snd) he).symm.trans hpt)
      let x := (vertexDeletedDartEquiv outer.snd).symm
        ⟨p,hps,hpt ▸ outer.adj.ne⟩
      have hx : R.outerDeletionRegion outer x := Or.inl (by
        change R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd)
          ((vertexDeletedDartEquiv outer.snd).symm _)).val
        rw [Equiv.apply_symm_apply]
        exact hp)
      refine ⟨(R.deleteVertex outer.snd).face x,R.outer_region_step outer hinner x hx,?_⟩
      have hh := congrArg Subtype.val ((R.deleteVertex outer.snd).face_source x)
      exact hh.trans hpt
    · let x := (vertexDeletedDartEquiv outer.snd).symm ⟨a,hv,ht⟩
      refine ⟨x,Or.inl ?_,rfl⟩
      change R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd)
        ((vertexDeletedDartEquiv outer.snd).symm _)).val
      rw [Equiv.apply_symm_apply]
      exact ha
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.fst.property,?_⟩
    by_cases ho : R.face.SameCycle outer ((vertexDeletedDartEquiv outer.snd) x).val
    · exact Or.inl ⟨_,ho,rfl⟩
    · right
      have ht := hinner _ ho
      have hh := congrArg (fun d : G.Dart => d.fst) ht
      rw [R.face_source] at hh
      have ha := (R.face (R.face ((vertexDeletedDartEquiv outer.snd) x).val)).adj
      rw [R.face_source, hx.resolve_left ho, hh] at ha
      exact ha
  · rintro ⟨hu,ho | hn⟩
    · obtain ⟨a,ha,rfl⟩ := ho
      exact old a ha hu
    · let d : G.Dart := ⟨(outer.snd,u),hn⟩
      by_cases he : d = outer.symm
      · have hu' : u = outer.fst := congrArg (fun a : G.Dart => a.snd) he
        obtain ⟨x,hx,hv⟩ := old outer Equiv.Perm.SameCycle.rfl outer.adj.ne
        exact ⟨x,hx,hv.trans hu'.symm⟩
      · have ht := R.outer_face_fan outer hsimple hinner d rfl he
        let x := R.sectorDeletedDart outer.snd d rfl ht
        have hx : R.outerDeletionRegion outer x := by
          right
          change (R.face (R.face (R.rotate d))).snd = outer.snd
          have hf : R.face d.symm = R.rotate d := by
            change R.rotate d.symm.symm = R.rotate d
            rw [SimpleGraph.Dart.symm_symm]
          rw [hf] at ht
          rw [ht]
          rfl
        refine ⟨(R.deleteVertex outer.snd).face x,R.outer_region_step outer hinner x hx,?_⟩
        have hh := congrArg Subtype.val ((R.deleteVertex outer.snd).face_source x)
        exact hh.trans (R.sector_endpoints_of_closed d ht).2

end JSP512Probe.RotationSystem
