import Probe.PendantFaceSteps

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G) (a : G.Dart) (v : V)
  (hv : v ∉ G.support)

/-- Pendant attachment preserves the face relation between all old darts. -/
theorem pendant_old_face_cycles (d e : G.Dart) :
    let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
    (addPendant G R a v hv).face.SameCycle (E (some (some d))) (E (some (some e))) ↔
      R.face.SameCycle d e := by
  classical
  dsimp only
  let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
  let : Fintype (addedGraph G a.fst v (isolated_ne_source G a v hv)).Dart :=
    Fintype.ofEquiv (Option (Option G.Dart)) E
  let σ := pendantRotation G R a * extendedReverse G
  have h := sameCycle_embedding σ (addPendant G R a v hv).face E E.injective
    (fun x => (pendant_face_embed G R a v hv x).symm) (some (some d)) (some (some e))
  rw [h]
  dsimp only [σ]
  rw [pendant_face_formula, insertAfter_sameCycle, insertAfter_sameCycle]

/-- The new reverse dart belongs exactly to the old attachment face. -/
theorem pendant_new_face_cycles (d : G.Dart) :
    let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
    (addPendant G R a v hv).face.SameCycle (E none) (E (some (some d))) ↔
      R.face.SameCycle a.symm d := by
  classical
  dsimp only
  let E := dartEquiv G a.fst v (isolated_ne_source G a v hv) (isolated_missing G a v hv)
  let : Fintype (addedGraph G a.fst v (isolated_ne_source G a v hv)).Dart :=
    Fintype.ofEquiv (Option (Option G.Dart)) E
  let σ := pendantRotation G R a * extendedReverse G
  have h := sameCycle_embedding σ (addPendant G R a v hv).face E E.injective
    (fun x => (pendant_face_embed G R a v hv x).symm) none (some (some d))
  rw [h]
  dsimp only [σ]
  rw [pendant_face_formula, insertAfter_new_cycle, insertAfter_new_cycle]

end JSP512Probe.EdgeInsertion
