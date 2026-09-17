import Probe.EarSeparation

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G) (a b : G.Dart)
  (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)

/-- The fixed old source corner rotates to the newest forward spoke. -/
theorem added_rotate_anchor :
    (addEdge G R a b hne hm).rotate (dartEquiv G a.fst b.fst hne hm (some (some a))) =
      dartEquiv G a.fst b.fst hne hm (some none) := by
  have hh := added_face_left G R a b hne hm
  change (addEdge G R a b hne hm).rotate
    ((dartEquiv G a.fst b.fst hne hm (some (some a.symm))).symm) = _ at hh
  exact hh

/-- Continuing along the next old boundary edge supplies the next ear path. -/
theorem added_next_path :
    let S := addEdge G R a b hne hm
    let E := dartEquiv G a.fst b.fst hne hm
    S.face (S.rotate (E (some (some a)))) =
      (E (some (some (R.rotate b).symm))).symm := by
  dsimp only
  rw [added_rotate_anchor, added_face_forward]
  rfl

/-- The retained source corner lies on the forward face automatically. -/
theorem added_next_corner :
    let S := addEdge G R a b hne hm
    let E := dartEquiv G a.fst b.fst hne hm
    S.face.SameCycle (E (some none)) (E (some (some a))).symm := by
  dsimp only
  have hh : (addEdge G R a b hne hm).face.SameCycle
      (dartEquiv G a.fst b.fst hne hm (some (some a.symm)))
      ((addEdge G R a b hne hm).face
        (dartEquiv G a.fst b.fst hne hm (some (some a.symm)))) :=
    Equiv.Perm.SameCycle.rfl.apply_right
  rw [added_face_left] at hh
  exact hh.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Adding one spoke cannot create a different missing spoke to the next
boundary vertex. -/
theorem added_next_missing (hmissing : ¬G.Adj a.fst (R.rotate b).snd) :
    ¬(addedGraph G a.fst b.fst hne).Adj a.fst (R.rotate b).snd := by
  intro h
  rcases h with h | h | h
  · exact hmissing h
  · exact (R.rotate b).fst_ne_snd ((R.source b).trans h.2.symm)
  · exact hne h.1

noncomputable local instance : DecidableRel (addedGraph G a.fst b.fst hne).Adj := Classical.decRel _

/-- Add the next spoke using the same source corner and the next boundary edge. -/
noncomputable def advanceFan (hnextne : a.fst ≠ (R.rotate b).snd)
    (hmissing : ¬G.Adj a.fst (R.rotate b).snd) :
    RotationSystem (addedGraph (addedGraph G a.fst b.fst hne)
      a.fst (R.rotate b).snd hnextne) :=
  addEdge (addedGraph G a.fst b.fst hne) (addEdge G R a b hne hm)
    (dartEquiv G a.fst b.fst hne hm (some (some a)))
    (dartEquiv G a.fst b.fst hne hm (some (some (R.rotate b).symm)))
    hnextne (added_next_missing G R a b hne hmissing)

/-- Two consecutive ear insertions preserve zero genus with no additional
cofaciality premise for the second step. -/
theorem advanceFan_genusZero (hnextne : a.fst ≠ (R.rotate b).snd)
    (hmissing : ¬G.Adj a.fst (R.rotate b).snd)
    (hpath : R.face (R.rotate a) = b.symm) (hz : R.HasGenusZero) :
    (advanceFan G R a b hne hm hnextne hmissing).HasGenusZero := by
  unfold advanceFan
  exact added_ear_genusZero _ _ _ _ _ _ (added_next_path G R a b hne hm)
    (added_ear_genusZero G R a b hne hm hpath hz)

/-- The canonical next spoke preserves the triangle created by the previous
spoke; its corner-placement premise is discharged by the construction. -/
theorem advanceFan_preserves_ear (hnextne : a.fst ≠ (R.rotate b).snd)
    (hmissing : ¬G.Adj a.fst (R.rotate b).snd)
    (hpath : R.face (R.rotate a) = b.symm) :
    let T := advanceFan G R a b hne hm hnextne hmissing
    let oldEar := dartEquiv G a.fst b.fst hne hm (some (some (R.rotate a)))
    let d := dartEquiv (addedGraph G a.fst b.fst hne) a.fst (R.rotate b).snd
      hnextne (added_next_missing G R a b hne hmissing) (some (some oldEar))
    T.face (T.face (T.face d)) = d := by
  exact added_ear_survives_next G R a b hne hm hpath _ _ hnextne
    (added_next_missing G R a b hne hmissing)
    (added_next_path G R a b hne hm) (added_next_corner G R a b hne hm)

end JSP512Probe.EdgeInsertion
