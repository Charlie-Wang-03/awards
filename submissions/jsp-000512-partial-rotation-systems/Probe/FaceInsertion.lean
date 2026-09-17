import Probe.EdgeInsertion
import Probe.SwapSplit

namespace JSP512Probe.EdgeInsertion
open CycleSurgery
variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (a b : G.Dart)

def cutFace : Equiv.Perm G.Dart := Equiv.swap (R.rotate a) (R.rotate b) * R.face

omit [Fintype V] [DecidableRel G.Adj] in
/-- Adding the two oriented sides of an edge equals swapping the old face
successors and subdividing the two resulting steps by the new darts. -/
theorem face_insertion_formula (hab : a ≠ b) :
    cornerRotation G R a b * extendedReverse G =
      insertAfter (insertAfter (cutFace G R a b) a.symm) (some b.symm) := by
  have hr : R.rotate a ≠ R.rotate b := fun h => hab (R.rotate.injective h)
  have hs : a.symm ≠ b.symm := fun h => hab (by simpa using congrArg SimpleGraph.Dart.symm h)
  have hc_a : cutFace G R a b a.symm = R.rotate b := by
    change Equiv.swap (R.rotate a) (R.rotate b) (R.rotate a.symm.symm) = _
    rw [SimpleGraph.Dart.symm_symm, Equiv.swap_apply_left]
  have hc_b : cutFace G R a b b.symm = R.rotate a := by
    change Equiv.swap (R.rotate a) (R.rotate b) (R.rotate b.symm.symm) = _
    rw [SimpleGraph.Dart.symm_symm, Equiv.swap_apply_right]
  apply Equiv.ext
  intro x
  cases x with
  | none =>
    change insertAfter (insertAfter R.rotate a) (some b) (some none) = _
    simp [insertAfter_old, hc_b, hs.symm]
  | some x =>
    cases x with
    | none =>
      change insertAfter (insertAfter R.rotate a) (some b) none = _
      simp [insertAfter_old, hab.symm, hc_a]
    | some d =>
      by_cases ha : d = a.symm
      · subst d
        change insertAfter (insertAfter R.rotate a) (some b) (some (some a.symm.symm)) = _
        simp [SimpleGraph.Dart.symm_symm, insertAfter_old, hab, hs]
      · by_cases hb : d = b.symm
        · subst d
          change insertAfter (insertAfter R.rotate a) (some b) (some (some b.symm.symm)) = _
          simp [SimpleGraph.Dart.symm_symm]
        · have hda : d.symm ≠ a := fun h => ha (by simpa using congrArg SimpleGraph.Dart.symm h)
          have hdb : d.symm ≠ b := fun h => hb (by simpa using congrArg SimpleGraph.Dart.symm h)
          have hc : cutFace G R a b d = R.rotate d.symm := by
            change Equiv.swap (R.rotate a) (R.rotate b) (R.rotate d.symm) = _
            exact Equiv.swap_apply_of_ne_of_ne (fun h => hda (R.rotate.injective h))
              (fun h => hdb (R.rotate.injective h))
          change insertAfter (insertAfter R.rotate a) (some b) (some (some d.symm)) = _
          simp [insertAfter_old, hda, hdb, ha, hb, hc]

/-- Subdividing the swapped face steps accounts for all new face orbits. -/
theorem added_face_count_eq_cut (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst) :
    (addEdge G R a b hne hm).faceCount =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (cutFace G R a b))) := by
  classical
  let e := dartEquiv G a.fst b.fst hne hm
  let τ := cornerRotation G R a b * extendedReverse G
  let F := (addEdge G R a b hne hm).face
  have hc : ∀ x, e (τ x) = F (e x) := fun x => (added_face_embed G R a b hne hm x).symm
  let qe : Quotient (Equiv.Perm.SameCycle.setoid τ) ≃
      Quotient (Equiv.Perm.SameCycle.setoid F) :=
    Quotient.congr e (fun x y => (sameCycle_embedding τ F e e.injective hc x y).symm)
  have hcount := Nat.card_congr qe
  change Nat.card (Quotient (Equiv.Perm.SameCycle.setoid τ)) =
    (addEdge G R a b hne hm).faceCount at hcount
  rw [← hcount]
  have hab : a ≠ b := fun h => hne (congrArg (fun d : G.Dart => d.fst) h)
  change Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
    (cornerRotation G R a b * extendedReverse G))) = _
  rw [face_insertion_formula G R a b hab, insertAfter_orbit_count, insertAfter_orbit_count]

/-- Joining two distinct nonadjacent source corners of the same face creates
exactly one extra face, before any genus or connectivity reasoning. -/
theorem cofacial_added_face_count (hne : a.fst ≠ b.fst) (hm : ¬G.Adj a.fst b.fst)
    (hf : R.face.SameCycle a.symm b.symm) :
    (addEdge G R a b hne hm).faceCount = R.faceCount + 1 := by
  rw [added_face_count_eq_cut G R a b hne hm]
  have hab : a ≠ b := fun h => hne (congrArg (fun d : G.Dart => d.fst) h)
  have hr : R.rotate a ≠ R.rotate b := fun h => hab (R.rotate.injective h)
  have h : R.face.SameCycle (R.rotate a) (R.rotate b) := by
    have hh := hf.apply_left.apply_right
    change R.face.SameCycle (R.rotate a.symm.symm) (R.rotate b.symm.symm) at hh
    simpa only [SimpleGraph.Dart.symm_symm] using hh
  exact swap_split_count R.face (R.rotate a) (R.rotate b) hr h

end JSP512Probe.EdgeInsertion
