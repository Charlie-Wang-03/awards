import Probe.SwapSplit

namespace JSP512Probe.RotationSystem
open CycleSurgery
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (d : G.Dart)

def firstFaceSwap : Equiv.Perm G.Dart := Equiv.swap d (R.rotate d) * R.face

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem firstFaceSwap_reverse : R.firstFaceSwap d d.symm = d := by
  change Equiv.swap d (R.rotate d) (R.rotate d.symm.symm) = d
  rw [SimpleGraph.Dart.symm_symm, Equiv.swap_apply_right]

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem firstFaceSwap_forward : R.firstFaceSwap d d = R.rotate d.symm := by
  change Equiv.swap d (R.rotate d) (R.rotate d.symm) = R.rotate d.symm
  exact Equiv.swap_apply_of_ne_of_ne (R.rotate_reverse_ne d)
    (fun h => d.symm_ne (R.rotate.injective h))

omit [Fintype V] [DecidableRel G.Adj] in
theorem second_swap_sameCycle :
    (R.firstFaceSwap d).SameCycle d.symm (R.rotate d.symm) := by
  have h : (R.firstFaceSwap d).SameCycle d.symm
      (R.firstFaceSwap d (R.firstFaceSwap d d.symm)) :=
    Equiv.Perm.SameCycle.rfl.apply_right.apply_right
  simpa only [firstFaceSwap_reverse, firstFaceSwap_forward] using h

theorem second_swap_count (ht : R.rotate d.symm ≠ d.symm) :
    (R.deleteEdge d).faceCount =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (R.firstFaceSwap d))) := by
  have h := swap_split_count (R.firstFaceSwap d) d.symm (R.rotate d.symm)
    ht.symm (R.second_swap_sameCycle d)
  have hc := R.ambient_face_count d
  rw [R.ambient_face_surgery d] at hc
  change Nat.card (Quotient (Equiv.Perm.SameCycle.setoid
    (Equiv.swap d.symm (R.rotate d.symm) * (Equiv.swap d (R.rotate d) * R.face)))) = _ at h
  rw [mul_assoc] at hc
  omega

/-- If neither endpoint rotation is a singleton, equal incident faces split. -/
theorem delete_face_count_same (hs : R.rotate d ≠ d) (ht : R.rotate d.symm ≠ d.symm)
    (hf : R.face.SameCycle d d.symm) :
    (R.deleteEdge d).faceCount = R.faceCount + 1 := by
  rw [R.second_swap_count d ht]
  have hh : R.face.SameCycle d (R.rotate d) := by
    have h := hf.apply_right
    change R.face.SameCycle d (R.rotate d.symm.symm) at h
    simpa only [SimpleGraph.Dart.symm_symm] using h
  exact swap_split_count R.face d (R.rotate d) hs.symm hh

/-- If neither endpoint rotation is a singleton, distinct incident faces merge. -/
theorem delete_face_count_different (ht : R.rotate d.symm ≠ d.symm)
    (hf : ¬R.face.SameCycle d d.symm) :
    R.faceCount = (R.deleteEdge d).faceCount + 1 := by
  rw [R.second_swap_count d ht]
  have hh : ¬R.face.SameCycle d (R.rotate d) := by
    intro h
    apply hf
    have he : R.face d.symm = R.rotate d := by
      change R.rotate d.symm.symm = R.rotate d
      rw [SimpleGraph.Dart.symm_symm]
    rw [← he] at h
    exact h.of_apply_right
  exact swap_cycle_count R.face d (R.rotate d) hh

theorem second_swap_fixed_count (ht : R.rotate d.symm = d.symm) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (R.firstFaceSwap d))) =
      (R.deleteEdge d).faceCount + 1 := by
  have hc := R.ambient_face_count d
  rw [R.ambient_face_surgery d, ht] at hc
  have he : Equiv.swap d.symm d.symm * Equiv.swap d (R.rotate d) * R.face =
      R.firstFaceSwap d := by
    apply Equiv.ext
    intro x
    simp [firstFaceSwap, Equiv.Perm.mul_apply]
  rw [he] at hc
  exact hc

omit [Fintype V] [DecidableRel G.Adj] in
theorem first_swap_fixed (hs : R.rotate d = d) : R.firstFaceSwap d = R.face := by
  apply Equiv.ext
  intro x
  simp [firstFaceSwap, hs, Equiv.Perm.mul_apply]

/-- Deleting a pendant edge leaves the face orbit count unchanged. -/
theorem delete_face_count_source_leaf (hs : R.rotate d = d)
    (ht : R.rotate d.symm ≠ d.symm) : (R.deleteEdge d).faceCount = R.faceCount := by
  rw [R.second_swap_count d ht, R.first_swap_fixed d hs]
  rfl

theorem delete_face_count_target_leaf (hs : R.rotate d ≠ d)
    (ht : R.rotate d.symm = d.symm) : (R.deleteEdge d).faceCount = R.faceCount := by
  have hf : R.face.SameCycle d (R.rotate d) := by
    have h : R.face.SameCycle d (R.face (R.face d)) :=
      Equiv.Perm.SameCycle.rfl.apply_right.apply_right
    have he : R.face d = d.symm := ht
    rw [he] at h
    change R.face.SameCycle d (R.rotate d.symm.symm) at h
    simpa only [SimpleGraph.Dart.symm_symm] using h
  have h₁ := swap_split_count R.face d (R.rotate d) hs.symm hf
  have h₂ := R.second_swap_fixed_count d ht
  change Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (R.firstFaceSwap d))) =
    R.faceCount + 1 at h₁
  omega

/-- An isolated edge contributes one dart-face; deleting it removes that face. -/
theorem delete_face_count_isolated_edge (hs : R.rotate d = d)
    (ht : R.rotate d.symm = d.symm) : R.faceCount = (R.deleteEdge d).faceCount + 1 := by
  have h := R.second_swap_fixed_count d ht
  rw [R.first_swap_fixed d hs] at h
  exact h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A fixed dart in the vertex rotation means its source has only one outgoing dart. -/
theorem rotate_fixed_iff_unique : R.rotate d = d ↔
    ∀ e : G.Dart, e.fst = d.fst → e = d := by
  constructor
  · intro h e he
    have hc : R.rotate.SameCycle d e := R.local_cycle d e he.symm
    exact (hc.eq_of_left h).symm
  · intro h
    exact h (R.rotate d) (R.source d)

end JSP512Probe.RotationSystem
