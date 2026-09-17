import Probe.CofacialInsertion

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G) (a b : G.Dart)
  (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)

/-- Old facial steps away from the two insertion corners are unchanged. -/
theorem added_face_old_away (d : G.Dart) (ha : d ≠ a.symm) (hb : d ≠ b.symm) :
    (addEdge G R a b hne hm).face (dartEquiv G a.fst b.fst hne hm (some (some d))) =
      dartEquiv G a.fst b.fst hne hm (some (some (R.face d))) := by
  have hda : d.symm ≠ a := fun h => ha (by simpa using congrArg SimpleGraph.Dart.symm h)
  have hdb : d.symm ≠ b := fun h => hb (by simpa using congrArg SimpleGraph.Dart.symm h)
  rw [added_face_embed]
  congr 1
  simp only [extendedReverse,Equiv.coe_fn_mk,cornerRotation,insertAfter_old,
    Option.some.injEq,ite_eq_right hdb,ite_eq_right hda]
  rfl

/-- The incoming left corner enters the new forward dart. -/
theorem added_face_left :
    (addEdge G R a b hne hm).face (dartEquiv G a.fst b.fst hne hm (some (some a.symm))) =
      dartEquiv G a.fst b.fst hne hm (some none) := by
  have hab : a ≠ b := fun h => hne (congrArg (fun d : G.Dart => d.fst) h)
  rw [added_face_embed]
  congr 1
  simp [extendedReverse,cornerRotation,insertAfter_old,hab]

/-- The incoming right corner enters the new reverse dart. -/
theorem added_face_right :
    (addEdge G R a b hne hm).face (dartEquiv G a.fst b.fst hne hm (some (some b.symm))) =
      dartEquiv G a.fst b.fst hne hm none := by
  rw [added_face_embed]
  congr 1
  simp [extendedReverse,cornerRotation]

/-- The new reverse dart returns to the first old side of the new ear. -/
theorem added_face_reverse :
    (addEdge G R a b hne hm).face (dartEquiv G a.fst b.fst hne hm none) =
      dartEquiv G a.fst b.fst hne hm (some (some (R.rotate a))) := by
  rw [added_face_embed]
  congr 1
  simp [extendedReverse,cornerRotation,insertAfter_old]

/-- The new forward dart continues along the old outer traversal. -/
theorem added_face_forward :
    (addEdge G R a b hne hm).face (dartEquiv G a.fst b.fst hne hm (some none)) =
      dartEquiv G a.fst b.fst hne hm (some (some (R.rotate b))) := by
  have hba : b ≠ a := fun h => hne (congrArg (fun d : G.Dart => d.fst) h).symm
  rw [added_face_embed]
  congr 1
  simp [extendedReverse,cornerRotation,insertAfter_old,hba]

/-- Adding the missing shortcut across two consecutive facial edges creates
an actual triangular face, with no assumption that other faces are triangular. -/
theorem added_ear_triangle (hpath : R.face (R.rotate a) = b.symm) :
    let S := addEdge G R a b hne hm
    let d := dartEquiv G a.fst b.fst hne hm (some (some (R.rotate a)))
    S.face (S.face (S.face d)) = d := by
  have ha : R.rotate a ≠ a.symm := by
    intro h
    have hh := congrArg (fun d : G.Dart => d.fst) h
    rw [R.source] at hh
    exact a.fst_ne_snd hh
  have hb : R.rotate a ≠ b.symm := by
    intro h
    exact R.face_ne_self (R.rotate a) (hpath.trans h.symm)
  dsimp only
  rw [added_face_old_away G R a b hne hm _ ha hb,hpath,
    added_face_right,added_face_reverse]

/-- Ear insertion preserves zero genus because its two corners are cofacial. -/
theorem added_ear_genusZero (hpath : R.face (R.rotate a) = b.symm) (hz : R.HasGenusZero) :
    (addEdge G R a b hne hm).HasGenusZero := by
  apply cofacial_genusZero G R a b hne hm _ hz
  have he : R.face a.symm = R.rotate a := by
    change R.rotate a.symm.symm = R.rotate a
    rw [SimpleGraph.Dart.symm_symm]
  have hh : R.face.SameCycle a.symm (R.face (R.face a.symm)) :=
    Equiv.Perm.SameCycle.rfl.apply_right.apply_right
  rwa [he,hpath] at hh
/-- Ear insertion leaves every triangular face outside the modified old face
unchanged, so successive fan steps do not destroy existing inner triangles. -/
theorem added_ear_preserves_triangle (hpath : R.face (R.rotate a) = b.symm)
    (d : G.Dart) (hd : ¬R.face.SameCycle a.symm d)
    (ht : R.face (R.face (R.face d)) = d) :
    let S := addEdge G R a b hne hm
    let x := dartEquiv G a.fst b.fst hne hm (some (some d))
    S.face (S.face (S.face x)) = x := by
  have he : R.face a.symm = R.rotate a := by
    change R.rotate a.symm.symm = R.rotate a
    rw [SimpleGraph.Dart.symm_symm]
  have hab : R.face.SameCycle a.symm b.symm := by
    have hh : R.face.SameCycle a.symm (R.face (R.face a.symm)) :=
      Equiv.Perm.SameCycle.rfl.apply_right.apply_right
    rwa [he,hpath] at hh
  have away : ∀ z, R.face.SameCycle d z → z ≠ a.symm ∧ z ≠ b.symm := by
    intro z hz
    constructor
    · intro h
      subst z
      exact hd hz.symm
    · intro h
      subst z
      exact hd (hab.trans hz.symm)
  have h0 := away d Equiv.Perm.SameCycle.rfl
  have h1 := away (R.face d) Equiv.Perm.SameCycle.rfl.apply_right
  have h2 := away (R.face (R.face d)) Equiv.Perm.SameCycle.rfl.apply_right.apply_right
  dsimp only
  rw [added_face_old_away G R a b hne hm d h0.1 h0.2,
    added_face_old_away G R a b hne hm (R.face d) h1.1 h1.2,
    added_face_old_away G R a b hne hm (R.face (R.face d)) h2.1 h2.2,ht]

end JSP512Probe.EdgeInsertion
