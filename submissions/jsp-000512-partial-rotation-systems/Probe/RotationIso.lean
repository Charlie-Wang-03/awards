import Probe.ComponentGenus

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transport darts along a graph isomorphism. -/
def isoDarts (e : G ≃g H) : G.Dart ≃ H.Dart where
  toFun d := ⟨(e d.fst,e d.snd),e.toHom.map_adj d.adj⟩
  invFun d := ⟨(e.symm d.fst,e.symm d.snd),e.symm.toHom.map_adj d.adj⟩
  left_inv _d := SimpleGraph.Dart.ext _ _ (Prod.ext (e.symm_apply_apply _) (e.symm_apply_apply _))
  right_inv _d := SimpleGraph.Dart.ext _ _ (Prod.ext (e.apply_symm_apply _) (e.apply_symm_apply _))

theorem isoDarts_reverse (e : G ≃g H) (d : G.Dart) : isoDarts e d.symm = (isoDarts e d).symm := rfl

variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  [DecidableRel G.Adj] [DecidableRel H.Adj] (R : RotationSystem G) (e : G ≃g H)

/-- The transported actual rotation, including its single-cycle source property. -/
noncomputable def mapIso : RotationSystem H := by
  let E := isoDarts e
  let σ : Equiv.Perm H.Dart := (E.symm.trans R.rotate).trans E
  have step : ∀ d, σ (E d) = E (R.rotate d) := by
    intro d
    change E (R.rotate (E.symm (E d))) = E (R.rotate d)
    rw [E.symm_apply_apply]
  refine ⟨σ,?_,?_⟩
  · intro x
    obtain ⟨d,rfl⟩ := E.surjective x
    rw [step]
    exact congrArg e (R.source d)
  · intro x y h
    obtain ⟨d,rfl⟩ := E.surjective x
    obtain ⟨f,rfl⟩ := E.surjective y
    apply (transport_cycles E.symm R.rotate (E d) (E f)).mpr
    simp only [Equiv.symm_apply_apply]
    exact R.local_cycle d f (e.injective h)

omit [Fintype W] [DecidableEq V] [DecidableEq W] [DecidableRel H.Adj] in
/-- Face traversal commutes with transport. -/
theorem mapIso_face (d : G.Dart) : (R.mapIso e).face (isoDarts e d) = isoDarts e (R.face d) := by
  change isoDarts e (R.rotate ((isoDarts e).symm (isoDarts e d).symm)) = _
  rw [← isoDarts_reverse,Equiv.symm_apply_apply]
  rfl

omit [DecidableEq V] [DecidableEq W] in
/-- The transported faces are exactly the original facial orbits. -/
theorem mapIso_face_cycles (d f : G.Dart) :
    (R.mapIso e).face.SameCycle (isoDarts e d) (isoDarts e f) ↔ R.face.SameCycle d f := by
  exact sameCycle_embedding R.face (R.mapIso e).face (isoDarts e) (isoDarts e).injective
    (fun d => (R.mapIso_face e d).symm) d f

omit [DecidableEq V] [DecidableEq W] in
/-- Transport preserves the length of each specified facial orbit. -/
theorem mapIso_faceLength (root : G.Dart) :
    (R.mapIso e).faceLength (isoDarts e root) = R.faceLength root := by
  classical
  let F : {d : G.Dart // R.face.SameCycle root d} ≃
      {d : H.Dart // (R.mapIso e).face.SameCycle (isoDarts e root) d} :=
    (isoDarts e).subtypeEquiv (fun d => (R.mapIso_face_cycles e root d).symm)
  rw [(R.mapIso e).faceLength_eq_card,R.faceLength_eq_card]
  exact (Nat.card_congr F).symm

omit [Fintype W] [DecidableEq V] [DecidableEq W] [DecidableRel H.Adj] in
/-- Three-step facial closure is preserved by the actual transported permutation. -/
theorem mapIso_triangle (d : G.Dart) (ht : R.face (R.face (R.face d)) = d) :
    (R.mapIso e).face ((R.mapIso e).face ((R.mapIso e).face (isoDarts e d))) = isoDarts e d := by
  rw [R.mapIso_face,R.mapIso_face,R.mapIso_face,ht]

omit [DecidableEq V] [DecidableEq W] in
/-- Isomorphic rotations have equal face counts. -/
theorem mapIso_faceCount : (R.mapIso e).faceCount = R.faceCount := by
  let E : R.FaceOrbit ≃ (R.mapIso e).FaceOrbit := Quotient.congr (isoDarts e)
    (fun d f => (R.mapIso_face_cycles e d f).symm)
  exact (Nat.card_congr E).symm

omit [DecidableEq V] [DecidableEq W] in
/-- Euler defect is invariant under graph-isomorphism transport. -/
theorem mapIso_eulerDefect : (R.mapIso e).eulerDefect = R.eulerDefect := by
  classical
  have hv := Fintype.card_congr e.toEquiv
  have hd := Fintype.card_congr (isoDarts e)
  rw [SimpleGraph.dart_card_eq_twice_card_edges,SimpleGraph.dart_card_eq_twice_card_edges] at hd
  have he : Nat.card G.edgeSet = Nat.card H.edgeSet := by
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hd
    omega
  let S : G.support ≃ H.support := {
    toFun := fun x => ⟨e x.val,by
      obtain ⟨w,hw⟩ := G.mem_support.mp x.property
      exact H.mem_support.mpr ⟨e w,e.toHom.map_adj hw⟩⟩
    invFun := fun x => ⟨e.symm x.val,by
      obtain ⟨w,hw⟩ := H.mem_support.mp x.property
      exact G.mem_support.mpr ⟨e.symm w,e.symm.toHom.map_adj hw⟩⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply _)
    right_inv := fun x => Subtype.ext (e.apply_symm_apply _) }
  let C : G.ConnectedComponent ≃ H.ConnectedComponent :=
    Quotient.congr (ra := G.reachableSetoid) (rb := H.reachableSetoid) e.toEquiv (by
      intro x y
      constructor
      · intro h; exact h.map e.toHom
      · intro h
        have hh := h.map e.symm.toHom
        change G.Reachable (e.symm (e x)) (e.symm (e y)) at hh
        change G.Reachable x y
        simpa only [e.symm_apply_apply] using hh)
  have hs := Nat.card_congr S
  have hc := Nat.card_congr C
  simp only [eulerDefect,supportSize,R.mapIso_faceCount e,← hv,← he,← hs,← hc]

omit [DecidableEq V] [DecidableEq W] in
/-- Transport preserves zero genus of the actual rotation. -/
theorem mapIso_genusZero (hz : R.HasGenusZero) : (R.mapIso e).HasGenusZero :=
  (R.mapIso_eulerDefect e).trans hz
end JSP512Probe.RotationSystem
