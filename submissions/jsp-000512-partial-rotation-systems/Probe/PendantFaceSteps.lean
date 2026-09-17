import Probe.PendantInsertion

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G) (a : G.Dart) (v : V)
  (hv : v ∉ G.support)

/-- Actual face conjugacy for the first edge connecting an isolated fan center. -/
theorem pendant_face_embed (x : Option (Option G.Dart)) :
    (addPendant G R a v hv).face
      (dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv) x) =
    dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
      (pendantRotation G R a (extendedReverse G x)) := by
  let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
  change E (pendantRotation G R a (E.symm ((E x).symm))) = _
  have hr : E (extendedReverse G x) = (E x).symm := embed_reverse G _ _ _ x
  rw [← hr,E.symm_apply_apply]

/-- The first attachment replaces the selected old step by a two-dart detour. -/
theorem pendant_face_anchor :
    let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
    (addPendant G R a v hv).face (E (some (some a.symm))) = E (some none) := by
  dsimp only
  rw [pendant_face_embed]
  congr 1
  simp [pendantRotation,extendedReverse]

theorem pendant_face_forward :
    let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
    (addPendant G R a v hv).face (E (some none)) = E none := by
  dsimp only
  rw [pendant_face_embed]
  rfl

/-- The new center's reverse dart follows the old outgoing boundary edge,
providing the two-edge path for the first triangular ear insertion. -/
theorem pendant_face_reverse :
    let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
    (addPendant G R a v hv).face (E none) = E (some (some (R.rotate a))) := by
  dsimp only
  rw [pendant_face_embed]
  congr 1

/-- All other old facial steps survive the initial attachment. -/
theorem pendant_face_old_away (d : G.Dart) (hd : d ≠ a.symm) :
    let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
    (addPendant G R a v hv).face (E (some (some d))) = E (some (some (R.face d))) := by
  have hn : d.symm ≠ a := fun h => hd (by simpa using congrArg SimpleGraph.Dart.symm h)
  dsimp only
  rw [pendant_face_embed]
  congr 1
  simp [pendantRotation,extendedReverse,insertAfter_old,hn,RotationSystem.face,RotationSystem.reverseDart]
end JSP512Probe.EdgeInsertion
