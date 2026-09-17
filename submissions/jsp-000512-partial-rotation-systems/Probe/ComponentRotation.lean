import Probe.DiskInstance

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)
  (A : Set V) (hA : ∀ u ∈ A, ∀ v, G.Adj u v → v ∈ A)

/-- Darts of a union of components correspond to old darts with source in it. -/
def closedDartEquiv : (G.induce A).Dart ≃ {d : G.Dart // d.fst ∈ A} where
  toFun d := ⟨⟨(d.fst.val,d.snd.val),d.adj⟩,d.fst.property⟩
  invFun d := ⟨(⟨d.val.fst,d.property⟩,⟨d.val.snd,hA _ d.property _ d.val.adj⟩),d.val.adj⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restrict the actual source rotation to a union of connected components. -/
noncomputable def restrictClosed : RotationSystem (G.induce A) := by
  classical
  let e := closedDartEquiv A hA
  let τ : Equiv.Perm {d : G.Dart // d.fst ∈ A} :=
    R.rotate.subtypeEquiv (fun d => by rw [R.source])
  let σ : Equiv.Perm (G.induce A).Dart := (e.trans τ).trans e.symm
  have hc : ∀ x y, σ.SameCycle x y ↔ x.fst = y.fst := by
    intro x y
    rw [transport_cycles e τ,subtype_cycles,R.sameCycle_iff_source]
    exact ⟨Subtype.ext,fun h => congrArg Subtype.val h⟩
  exact ⟨σ,fun _ => (hc _ _).mp Equiv.Perm.SameCycle.rfl.apply_left,
    fun _ _ h => (hc _ _).mpr h⟩

omit [DecidableEq V] in
/-- Component restriction preserves each face step exactly. -/
theorem restrictClosed_face (x : (G.induce A).Dart) :
    ((closedDartEquiv A hA) ((R.restrictClosed A hA).face x)).val =
      R.face ((closedDartEquiv A hA) x).val := by
  change ((closedDartEquiv A hA) ((closedDartEquiv A hA).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

omit [DecidableEq V] in
/-- Face cycles of the component restriction are exactly the old face cycles. -/
theorem restrictClosed_face_cycles (x y : (G.induce A).Dart) :
    (R.restrictClosed A hA).face.SameCycle x y ↔
      R.face.SameCycle ((closedDartEquiv A hA) x).val ((closedDartEquiv A hA) y).val := by
  classical
  let f := fun x => ((closedDartEquiv A hA) x).val
  have hi : Function.Injective f := fun x y h => (closedDartEquiv A hA).injective (Subtype.ext h)
  exact (sameCycle_embedding (R.restrictClosed A hA).face R.face f hi
    (R.restrictClosed_face A hA) x y).symm

include hA in
omit [DecidableEq V] in
/-- A whole old face remains in the closed vertex set of its initial dart. -/
theorem face_cycle_in_closed (d e : G.Dart) (hd : d.fst ∈ A) (he : R.face.SameCycle d e) :
    e.fst ∈ A := by
  obtain ⟨n,rfl⟩ := he.exists_nat_pow_eq
  clear he
  induction n with
  | zero => exact hd
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,R.face_source]
    exact hA _ ih _ ((R.face ^ n) d).adj

omit [DecidableEq V] in
/-- Component restriction preserves the entire size of every face it contains. -/
theorem restrictClosed_faceLength (root : (G.induce A).Dart) :
    (R.restrictClosed A hA).faceLength root = R.faceLength ((closedDartEquiv A hA) root).val := by
  classical
  let f : {x : (G.induce A).Dart // (R.restrictClosed A hA).face.SameCycle root x} →
      {d : G.Dart // R.face.SameCycle ((closedDartEquiv A hA) root).val d} :=
    fun x => ⟨((closedDartEquiv A hA) x.val).val,(R.restrictClosed_face_cycles A hA root x.val).mp x.property⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply (closedDartEquiv A hA).injective
    have hh : ((closedDartEquiv A hA) x.val).val = ((closedDartEquiv A hA) y.val).val :=
      congrArg (fun z : {d : G.Dart // R.face.SameCycle ((closedDartEquiv A hA) root).val d} => z.val) h
    exact Subtype.ext hh
  have hs : Function.Surjective f := by
    intro d
    have hm := R.face_cycle_in_closed A hA _ d.val ((closedDartEquiv A hA) root).property d.property
    let x := (closedDartEquiv A hA).symm ⟨d.val,hm⟩
    have he : ((closedDartEquiv A hA) x).val = d.val := by
      change ((closedDartEquiv A hA) ((closedDartEquiv A hA).symm _)).val = _
      rw [Equiv.apply_symm_apply]
    have hx := (R.restrictClosed_face_cycles A hA root x).mpr (he.symm ▸ d.property)
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  rw [(R.restrictClosed A hA).faceLength_eq_card,R.faceLength_eq_card]
  exact Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)

omit [DecidableEq V] in
/-- Inner triangular closure transfers to the actual component restriction. -/
theorem restrictClosed_triangle (x : (G.induce A).Dart)
    (ht : R.face (R.face (R.face ((closedDartEquiv A hA) x).val)) =
      ((closedDartEquiv A hA) x).val) :
    (R.restrictClosed A hA).face ((R.restrictClosed A hA).face
      ((R.restrictClosed A hA).face x)) = x := by
  apply (closedDartEquiv A hA).injective
  apply Subtype.ext
  rw [R.restrictClosed_face,R.restrictClosed_face,R.restrictClosed_face]
  exact ht

/-- The restriction specializes to the actual induced graph of any component. -/
noncomputable def componentRotation (C : G.ConnectedComponent) : RotationSystem C.toSimpleGraph :=
  R.restrictClosed C.supp (fun _ hu _ huv => C.mem_supp_of_adj_mem_supp hu huv)
end JSP512Probe.RotationSystem
