import Probe.FiberPermutation
import Probe.TriangularNeighborOrder

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G) (v : V)

/-- At each neighbor, remove the unique dart pointing to the deleted vertex. -/
def vertexLocalRotation (u : V) : Equiv.Perm G.Dart :=
  if h : G.Adj u v then eraseAt R.rotate ⟨(u,v),h⟩ else R.rotate

omit [Fintype V] in
theorem vertexLocal_source (u : V) (d : G.Dart) :
    (R.vertexLocalRotation v u d).fst = d.fst := by
  unfold vertexLocalRotation
  split_ifs with h
  · let a : G.Dart := ⟨(u,v),h⟩
    by_cases hd : d = a
    · subst d
      exact congrArg (fun x : G.Dart => x.fst) (eraseAt_self R.rotate a)
    · rw [eraseAt_apply _ _ _ hd]
      split_ifs with he
      · rw [R.source, ← he, R.source]
      · exact R.source d
  · exact R.source d

def vertexErasedRotation : Equiv.Perm G.Dart :=
  fiberPermutation (fun d : G.Dart => d.fst) (R.vertexLocalRotation v) (R.vertexLocal_source v)

abbrev VertexSurvivor := {d : G.Dart // d.fst ≠ v ∧ d.snd ≠ v}
abbrev VertexDeletedGraph := G.induce {u | u ≠ v}

omit [Fintype V] in
theorem vertexErased_source (d : G.Dart) : (R.vertexErasedRotation v d).fst = d.fst :=
  R.vertexLocal_source v d.fst d

omit [Fintype V] in
theorem vertexErased_incoming_fixed (d : G.Dart) (hd : d.snd = v) :
    R.vertexErasedRotation v d = d := by
  change R.vertexLocalRotation v d.fst d = d
  have ha : G.Adj d.fst v := hd ▸ d.adj
  unfold vertexLocalRotation
  rw [dite_eq_left ha]
  have he : (⟨(d.fst,v),ha⟩ : G.Dart) = d := SimpleGraph.Dart.ext _ _ (Prod.ext rfl hd.symm)
  rw [he,eraseAt_self]

omit [Fintype V] in
theorem vertex_survives_iff (d : G.Dart) :
    (d.fst ≠ v ∧ d.snd ≠ v) ↔
      (R.vertexErasedRotation v d).fst ≠ v ∧ (R.vertexErasedRotation v d).snd ≠ v := by
  rw [R.vertexErased_source]
  constructor
  · rintro ⟨hs,ht⟩
    refine ⟨hs,?_⟩
    intro h
    have hf := R.vertexErased_incoming_fixed v (R.vertexErasedRotation v d) h
    have he := (R.vertexErasedRotation v).injective hf
    exact ht (by rw [← he]; exact h)
  · rintro ⟨hs,ht⟩
    refine ⟨hs,?_⟩
    intro h
    rw [R.vertexErased_incoming_fixed v d h] at ht
    exact ht h

def vertexDeletedDartEquiv : (VertexDeletedGraph (G := G) v).Dart ≃ VertexSurvivor (G := G) v where
  toFun d := ⟨⟨(d.fst.val,d.snd.val),d.adj⟩,d.fst.property,d.snd.property⟩
  invFun d := ⟨(⟨d.val.fst,d.property.1⟩,⟨d.val.snd,d.property.2⟩),d.val.adj⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual rotation after deleting a vertex, on the induced graph's own dart type. -/
noncomputable def deleteVertex : RotationSystem (VertexDeletedGraph (G := G) v) := by
  let e := vertexDeletedDartEquiv (G := G) v
  let τ : Equiv.Perm (VertexSurvivor (G := G) v) := (R.vertexErasedRotation v).subtypeEquiv (R.vertex_survives_iff v)
  let σ : Equiv.Perm (VertexDeletedGraph (G := G) v).Dart := (e.trans τ).trans e.symm
  have hc : ∀ x y, σ.SameCycle x y ↔ x.fst = y.fst := by
    intro x y
    rw [transport_cycles e τ, subtype_cycles]
    unfold vertexErasedRotation
    rw [fiberPermutation_cycles]
    change (R.vertexLocalRotation v x.fst.val).SameCycle (e x).val (e y).val ↔ _
    unfold vertexLocalRotation
    split_ifs with ha
    · have hx : (e x).val ≠ ⟨(x.fst.val,v),ha⟩ := by
        intro h
        exact x.snd.property (congrArg (fun d : G.Dart => d.snd) h)
      have hy : (e y).val ≠ ⟨(x.fst.val,v),ha⟩ := by
        intro h
        exact y.snd.property (congrArg (fun d : G.Dart => d.snd) h)
      rw [eraseAt_sameCycle_iff _ _ _ _ hx hy, R.sameCycle_iff_source]
      exact ⟨Subtype.ext,fun h => congrArg Subtype.val h⟩
    · rw [R.sameCycle_iff_source]
      exact ⟨Subtype.ext,fun h => congrArg Subtype.val h⟩
  exact ⟨σ,fun _ => (hc _ _).mp Equiv.Perm.SameCycle.rfl.apply_left,
    fun _ _ h => (hc _ _).mpr h⟩

/-- The deleted face successor is the sourcewise bypass applied to the reverse dart. -/
theorem vertex_deleted_face (x : (VertexDeletedGraph (G := G) v).Dart) :
    ((vertexDeletedDartEquiv v) ((R.deleteVertex v).face x)).val =
      R.vertexErasedRotation v ((vertexDeletedDartEquiv v) x).val.symm := by
  change ((vertexDeletedDartEquiv v)
    ((vertexDeletedDartEquiv v).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

omit [Fintype V] in
/-- A surviving dart skips exactly the single removed incoming dart at its source. -/
theorem vertexErased_apply (d : G.Dart) (hd : d.snd ≠ v) :
    R.vertexErasedRotation v d =
      if (R.rotate d).snd = v then R.rotate (R.rotate d) else R.rotate d := by
  change R.vertexLocalRotation v d.fst d = _
  unfold vertexLocalRotation
  split_ifs with ha ht
  · let a : G.Dart := ⟨(d.fst,v),ha⟩
    have hn : d ≠ a := fun h => hd (congrArg (fun e : G.Dart => e.snd) h)
    have he : R.rotate d = a := SimpleGraph.Dart.ext _ _ (Prod.ext (R.source d) ht)
    rw [eraseAt_apply _ _ _ hn, ite_eq_left he, ← he]
  · let a : G.Dart := ⟨(d.fst,v),ha⟩
    have hn : d ≠ a := fun h => hd (congrArg (fun e : G.Dart => e.snd) h)
    have he : R.rotate d ≠ a := fun h => ht (congrArg (fun e : G.Dart => e.snd) h)
    rw [eraseAt_apply _ _ _ hn, ite_eq_right he]
  · rename_i ht
    have hh := (R.rotate d).adj
    rw [R.source, ht] at hh
    exact False.elim (ha hh)
  · rfl

/-- Exact face-splicing rule on the actual vertex-deleted graph. -/
theorem vertex_deleted_face_formula (x : (VertexDeletedGraph (G := G) v).Dart) :
    ((vertexDeletedDartEquiv v) ((R.deleteVertex v).face x)).val =
      if (R.face ((vertexDeletedDartEquiv v) x).val).snd = v then
        R.rotate (R.face ((vertexDeletedDartEquiv v) x).val)
      else R.face ((vertexDeletedDartEquiv v) x).val := by
  rw [R.vertex_deleted_face]
  exact R.vertexErased_apply v _ ((vertexDeletedDartEquiv v) x).property.1

end JSP512Probe.RotationSystem
