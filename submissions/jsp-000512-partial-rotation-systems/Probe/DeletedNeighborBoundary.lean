import Probe.FanSplicing

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (v : V)
  (htri : ∀ d, R.face (R.face (R.face d)) = d)

/-- All sides opposite the removed vertex in its incident triangular sectors. -/
def boundarySector (d : {d : G.Dart // d.fst = v}) :
    (VertexDeletedGraph (G := G) v).Dart :=
  R.sectorDeletedDart v d.val d.property (htri d.val.symm)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem boundarySector_injective : Function.Injective (R.boundarySector v htri) := by
  intro d e h
  have hh := congrArg (fun x : (VertexDeletedGraph (G := G) v).Dart => x.snd.val) h
  change (R.face (R.rotate d.val)).snd = (R.face (R.rotate e.val)).snd at hh
  rw [(R.triangular_sector_endpoints htri d.val).2,
    (R.triangular_sector_endpoints htri e.val).2] at hh
  apply Subtype.ext
  exact SimpleGraph.Dart.ext _ _ (Prod.ext (d.property.trans e.property.symm) hh)

/-- The new face traverses the sectors in inverse rotation order. -/
theorem boundarySector_step (d : {d : G.Dart // d.fst = v}) :
    R.boundarySector v htri ((R.sourceRotation v).symm d) =
      (R.deleteVertex v).face (R.boundarySector v htri d) := by
  symm
  apply R.sector_predecessor_step
  exact congrArg Subtype.val ((R.sourceRotation v).apply_symm_apply d)

/-- The entire new face consists precisely of the sides opposite the removed vertex. -/
theorem deleted_boundary_orbit (root : {d : G.Dart // d.fst = v})
    (x : (VertexDeletedGraph (G := G) v).Dart) :
    (R.deleteVertex v).face.SameCycle (R.boundarySector v htri root) x ↔
      ∃ d : {d : G.Dart // d.fst = v}, R.boundarySector v htri d = x := by
  let σ := (R.sourceRotation v).symm
  let F := (R.deleteVertex v).face
  let f := R.boundarySector v htri
  have hstep : ∀ d, f (σ d) = F (f d) := R.boundarySector_step v htri
  have hp : ∀ n : ℕ, f ((σ ^ n) root) = (F ^ n) (f root) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        hstep, ih]
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(σ ^ n) root,(hp n).trans hn⟩
  · rintro ⟨d,rfl⟩
    have hc : (R.sourceRotation v).SameCycle root d := by
      apply (subtype_cycles R.rotate _ (fun d => by rw [R.source]) _ _).mpr
      exact R.local_cycle _ _ (root.property.trans d.property.symm)
    exact (sameCycle_embedding σ F f (R.boundarySector_injective v htri)
      (R.boundarySector_step v htri) root d).mpr hc.inv

/-- The new facial boundary has exactly the original neighbor set as its vertices. -/
theorem deleted_boundary_vertices (root : {d : G.Dart // d.fst = v}) (u : V) :
    (∃ x : (VertexDeletedGraph (G := G) v).Dart,
      (R.deleteVertex v).face.SameCycle (R.boundarySector v htri root) x ∧ x.fst.val = u) ↔
      G.Adj v u := by
  constructor
  · rintro ⟨x,hx,hu⟩
    obtain ⟨d,rfl⟩ := (R.deleted_boundary_orbit v htri root x).mp hx
    change (R.face (R.rotate d.val)).fst = u at hu
    rw [R.face_source] at hu
    have ha := (R.rotate d.val).adj
    rw [R.source,d.property,hu] at ha
    exact ha
  · intro ha
    let e : G.Dart := ⟨(v,u),ha⟩
    have hd : (R.rotate.symm e).fst = v := by
      have hh := R.source (R.rotate.symm e)
      rw [R.rotate.apply_symm_apply] at hh
      exact hh.symm
    let d : {d : G.Dart // d.fst = v} := ⟨R.rotate.symm e,hd⟩
    refine ⟨R.boundarySector v htri d,
      (R.deleted_boundary_orbit v htri root _).mpr ⟨d,rfl⟩,?_⟩
    change (R.face (R.rotate (R.rotate.symm e))).fst = u
    rw [R.rotate.apply_symm_apply,R.face_source]

/-- The new boundary visits each surviving neighbor exactly once. -/
theorem deleted_boundary_source_injective (root : {d : G.Dart // d.fst = v})
    (x y : (VertexDeletedGraph (G := G) v).Dart)
    (hx : (R.deleteVertex v).face.SameCycle (R.boundarySector v htri root) x)
    (hy : (R.deleteVertex v).face.SameCycle (R.boundarySector v htri root) y)
    (hxy : x.fst = y.fst) : x = y := by
  obtain ⟨d,rfl⟩ := (R.deleted_boundary_orbit v htri root x).mp hx
  obtain ⟨e,rfl⟩ := (R.deleted_boundary_orbit v htri root y).mp hy
  have hh := congrArg Subtype.val hxy
  change (R.face (R.rotate d.val)).fst = (R.face (R.rotate e.val)).fst at hh
  rw [R.face_source,R.face_source] at hh
  have he : R.rotate d.val = R.rotate e.val := SimpleGraph.Dart.ext _ _
    (Prod.ext ((R.source d.val).trans (d.property.trans (e.property.symm.trans (R.source e.val).symm))) hh)
  have hd : d = e := Subtype.ext (R.rotate.injective he)
  rw [hd]

/-- Outside the new boundary orbit, every old face step is unchanged. -/
theorem deleted_nonboundary_step (root : {d : G.Dart // d.fst = v})
    (x : (VertexDeletedGraph (G := G) v).Dart)
    (hx : ¬(R.deleteVertex v).face.SameCycle (R.boundarySector v htri root) x) :
    ((vertexDeletedDartEquiv v) ((R.deleteVertex v).face x)).val =
      R.face ((vertexDeletedDartEquiv v) x).val := by
  let a := ((vertexDeletedDartEquiv v) x).val
  have hn : (R.face a).snd ≠ v := by
    intro ht
    let d : {d : G.Dart // d.fst = v} := ⟨(R.face a).symm,ht⟩
    have he : R.boundarySector v htri d = x := by
      apply (vertexDeletedDartEquiv v).injective
      apply Subtype.ext
      change R.face (R.rotate (R.face a).symm) = a
      change R.face (R.face (R.face a)) = a
      exact htri a
    exact hx ((R.deleted_boundary_orbit v htri root x).mpr ⟨d,he⟩)
  rw [R.vertex_deleted_face_formula,ite_eq_right hn]

/-- Every face other than the new neighbor boundary retains triangular closure. -/
theorem deleted_nonboundary_triangular (root : {d : G.Dart // d.fst = v})
    (x : (VertexDeletedGraph (G := G) v).Dart)
    (hx : ¬(R.deleteVertex v).face.SameCycle (R.boundarySector v htri root) x) :
    (R.deleteVertex v).face ((R.deleteVertex v).face ((R.deleteVertex v).face x)) = x := by
  let F := (R.deleteVertex v).face
  have hn₁ : ¬F.SameCycle (R.boundarySector v htri root) (F x) :=
    fun h => hx h.of_apply_right
  have hn₂ : ¬F.SameCycle (R.boundarySector v htri root) (F (F x)) :=
    fun h => hn₁ h.of_apply_right
  apply (vertexDeletedDartEquiv v).injective
  apply Subtype.ext
  rw [R.deleted_nonboundary_step v htri root (F (F x)) hn₂,
    R.deleted_nonboundary_step v htri root (F x) hn₁,
    R.deleted_nonboundary_step v htri root x hx]
  exact htri _

/-- The new boundary length equals the degree of the removed vertex. -/
theorem deleted_boundary_length (root : {d : G.Dart // d.fst = v}) :
    (R.deleteVertex v).faceLength (R.boundarySector v htri root) = G.degree v := by
  classical
  let A := {x : (VertexDeletedGraph (G := G) v).Dart //
    (R.deleteVertex v).face.SameCycle (R.boundarySector v htri root) x}
  let f : A → G.neighborSet v := fun x => ⟨x.val.fst.val,
    (R.deleted_boundary_vertices v htri root x.val.fst.val).mp ⟨x.val,x.property,rfl⟩⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply R.deleted_boundary_source_injective v htri root x.val y.val x.property y.property
    exact Subtype.ext (congrArg (fun z : G.neighborSet v => z.val) h)
  have hu : Function.Surjective f := by
    intro u
    obtain ⟨x,hx,he⟩ := (R.deleted_boundary_vertices v htri root u.val).mpr u.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  rw [(R.deleteVertex v).faceLength_eq_card]
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hi,hu⟩)
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using hc

end JSP512Probe.RotationSystem
