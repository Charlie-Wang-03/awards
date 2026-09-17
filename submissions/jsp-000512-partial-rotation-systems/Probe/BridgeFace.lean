import Probe.FaceDeletionCount
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace JSP512Probe.RotationSystem
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (d : G.Dart)

/-- Distinct incident face orbits give a path between the endpoints after deletion. -/
theorem reachable_of_different_faces (hf : ¬R.face.SameCycle d d.symm) :
    (DeletedGraph d).Reachable d.fst d.snd := by
  have hstep : ∀ x : G.Dart, R.face.SameCycle d x →
      (DeletedGraph d).Reachable d.snd x.fst →
      (DeletedGraph d).Reachable d.snd (R.face x).fst := by
    intro x hx hr
    rw [R.face_source]
    by_cases he : x = d
    · subst x
      exact SimpleGraph.Reachable.refl _
    · have hs : x ≠ d.symm := fun h => hf (h ▸ hx)
      have ha : (DeletedGraph d).Adj x.fst x.snd := by
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨x.adj, ?_⟩
        change ¬x.edge = d.edge
        rw [SimpleGraph.dart_edge_eq_iff x d]
        exact not_or.mpr ⟨he, hs⟩
      exact hr.trans ha.reachable
  have hp : ∀ n : ℕ, (DeletedGraph d).Reachable d.snd ((R.face ^ (n+1)) d).fst := by
    intro n
    induction n with
    | zero =>
      simp only [zero_add, pow_one, R.face_source]
      exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hstep _ Equiv.Perm.SameCycle.rfl.pow_right ih
  have hi : R.face.SameCycle d (R.face.symm d) := Equiv.Perm.SameCycle.rfl.symm_apply_right
  obtain ⟨n, hn⟩ := hi.exists_nat_pow_eq
  have h := hp n
  rw [pow_succ', Equiv.Perm.mul_apply, hn, Equiv.apply_symm_apply] at h
  exact h.symm

/-- Every bridge has both directed sides on the same face, without a genus assumption. -/
theorem bridge_same_face (hb : G.IsBridge d.edge) : R.face.SameCycle d d.symm := by
  by_contra h
  exact hb (R.reachable_of_different_faces d h)

/-- A bridge with two nonsingleton endpoint rotations splits its face on deletion. -/
theorem bridge_face_count (hb : G.IsBridge d.edge)
    (hs : R.rotate d ≠ d) (ht : R.rotate d.symm ≠ d.symm) :
    (R.deleteEdge d).faceCount = R.faceCount + 1 :=
  R.delete_face_count_same d hs ht (R.bridge_same_face d hb)

end JSP512Probe.RotationSystem
