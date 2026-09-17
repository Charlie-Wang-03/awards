import Probe.FanStartRoute
import Probe.PendantFaceOrbits

namespace JSP512Probe.RotationSystem
open EdgeInsertion CycleSurgery
variable {V : Type*} (G : SimpleGraph V)

/-- Every initialized dart is old or one of the two orientations of the spoke. -/
theorem startFan_dart_cases (a : G.Dart) (x : (fanStartGraph G a).Dart) :
    x = startAnchor G a ∨ x = (startAnchor G a).symm ∨ ∃ d, x = startOldDart G a d := by
  let E := dartEquiv (withIsolate G) (some a.fst) none (Option.some_ne_none _)
    (isolated_missing (withIsolate G) (isolateDarts G a) none (withIsolate_none_support G))
  obtain ⟨y, rfl⟩ := E.surjective x
  cases y with
  | none => exact Or.inl rfl
  | some y =>
    cases y with
    | none => exact Or.inr (Or.inl rfl)
    | some d =>
      obtain ⟨e, rfl⟩ := (isolateDarts G).surjective d
      exact Or.inr (Or.inr ⟨e, rfl⟩)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (R : RotationSystem G)

/-- Both new spoke orientations lie in the same selected outer face. -/
theorem startFan_face_forward (a : G.Dart) :
    (startFan G R a).face (startAnchor G a).symm = startAnchor G a := by
  classical
  exact pendant_face_forward (withIsolate G) (R.addIsolate) (isolateDarts G a)
    none (withIsolate_none_support G)

/-- Exact old-dart membership in the initialized outer face. -/
theorem startFan_outer_old_iff (a d : G.Dart) :
    (startFan G R a).face.SameCycle (startAnchor G a).symm (startOldDart G a d) ↔
      R.face.SameCycle a.symm d := by
  classical
  rw [← Equiv.Perm.sameCycle_apply_left, startFan_face_forward]
  have hh := pendant_new_face_cycles (withIsolate G) (R.addIsolate) (isolateDarts G a)
    none (withIsolate_none_support G) (isolateDarts G d)
  dsimp only at hh
  change (startFan G R a).face.SameCycle (startAnchor G a) (startOldDart G a d) ↔
    (R.addIsolate).face.SameCycle (isolateDarts G a.symm) (isolateDarts G d) at hh
  let : Fintype (withIsolate G).Dart := Fintype.ofEquiv G.Dart (isolateDarts G)
  exact hh.trans (sameCycle_embedding R.face (R.addIsolate).face (isolateDarts G)
    (isolateDarts G).injective (fun x => (addIsolate_face G R x).symm) a.symm d)

/-- Every old triangular face outside the attachment face survives. -/
theorem startFan_old_triangle (a d : G.Dart) (hd : ¬R.face.SameCycle a.symm d)
    (ht : R.face (R.face (R.face d)) = d) :
    (startFan G R a).face ((startFan G R a).face
      ((startFan G R a).face (startOldDart G a d))) = startOldDart G a d := by
  have away : ∀ x, R.face.SameCycle d x → x ≠ a.symm := by
    intro x hx hh
    subst x
    exact hd hx.symm
  rw [startFan_face_old G R a d (away d Equiv.Perm.SameCycle.rfl),
    startFan_face_old G R a (R.face d) (away _ Equiv.Perm.SameCycle.rfl.apply_right),
    startFan_face_old G R a (R.face (R.face d))
      (away _ Equiv.Perm.SameCycle.rfl.apply_right.apply_right), ht]

/-- Initialization preserves triangulation of every non-outer face; its
new spoke contributes only to the chosen outer face. -/
theorem startFan_inner (a : G.Dart)
    (hi : ∀ d, ¬R.face.SameCycle a.symm d → R.face (R.face (R.face d)) = d) :
    ∀ x, ¬(startFan G R a).face.SameCycle (startAnchor G a).symm x →
      (startFan G R a).face ((startFan G R a).face ((startFan G R a).face x)) = x := by
  intro x hx
  rcases startFan_dart_cases G a x with rfl | rfl | ⟨d, rfl⟩
  · exfalso
    apply hx
    have hh : (startFan G R a).face.SameCycle (startAnchor G a).symm
        ((startFan G R a).face (startAnchor G a).symm) := Equiv.Perm.SameCycle.rfl.apply_right
    rwa [startFan_face_forward] at hh
  · exact False.elim (hx Equiv.Perm.SameCycle.rfl)
  · have hd : ¬R.face.SameCycle a.symm d := fun hh =>
      hx ((startFan_outer_old_iff G R a d).mpr hh)
    exact startFan_old_triangle G R a d hd (hi d hd)

end JSP512Probe.RotationSystem
