import Probe.DeletionSupport

namespace JSP512Probe.RotationSystem
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
  [DecidableRel G.Adj] (R : RotationSystem G) (d : G.Dart)

/-- Twice the combinatorial genus, summed over components. Isolated vertices
are accounted for by the difference between the vertex count and support size.
Nonnegativity is not part of this definition. -/
noncomputable def eulerDefect : ℤ :=
  2 * (Nat.card G.ConnectedComponent : ℤ) - 2 * Fintype.card V +
    supportSize (G := G) + Nat.card G.edgeSet - R.faceCount

theorem edge_count_delete : Nat.card G.edgeSet = Nat.card (DeletedGraph d).edgeSet + 1 := by
  classical
  have he : d.edge ∈ G.edgeFinset := by simp [SimpleGraph.Dart.edge, d.adj]
  have hc := Finset.card_erase_add_one he
  have hd : (DeletedGraph d).edgeFinset = G.edgeFinset.erase d.edge := by
    ext e
    simp [DeletedGraph, SimpleGraph.mem_edgeFinset, and_comm]
  rw [← hd] at hc
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Nat.card_eq_fintype_card] using hc.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem nonbridge_rotations (hb : ¬G.IsBridge d.edge) :
    R.rotate d ≠ d ∧ R.rotate d.symm ≠ d.symm := by
  have hr : (DeletedGraph d).Reachable d.fst d.snd := Classical.not_not.mp hb
  exact ⟨(R.source_survives_iff d).mp (SimpleGraph.mem_support_of_reachable d.fst_ne_snd hr),
    (R.target_survives_iff d).mp (SimpleGraph.mem_support_of_reachable d.snd_ne_fst hr.symm)⟩

/-- Deleting a bridge leaves the corrected Euler defect unchanged. -/
theorem bridge_defect (hb : G.IsBridge d.edge) :
    R.eulerDefect = (R.deleteEdge d).eulerDefect := by
  have hc := bridge_component_count d hb
  have he := edge_count_delete d
  have hv := R.supportSize_delete d
  unfold eulerDefect
  by_cases hs : R.rotate d = d <;> by_cases ht : R.rotate d.symm = d.symm
  · have hf := R.delete_face_count_isolated_edge d hs ht
    simp only [ite_eq_left hs, ite_eq_left ht] at hv
    omega
  · have hf := R.delete_face_count_source_leaf d hs ht
    simp only [ite_eq_left hs, ite_eq_right ht] at hv
    omega
  · have hf := R.delete_face_count_target_leaf d hs ht
    simp only [ite_eq_right hs, ite_eq_left ht] at hv
    omega
  · have hf := R.bridge_face_count d hb hs ht
    simp only [ite_eq_right hs, ite_eq_right ht] at hv
    omega

/-- A nonbridge either preserves defect or reduces it by two on deletion. -/
theorem nonbridge_defect (hb : ¬G.IsBridge d.edge) :
    R.eulerDefect = (R.deleteEdge d).eulerDefect ∨
      R.eulerDefect = (R.deleteEdge d).eulerDefect + 2 := by
  obtain ⟨hs, ht⟩ := R.nonbridge_rotations d hb
  have hc := nonbridge_component_count d hb
  have he := edge_count_delete d
  have hv := R.supportSize_delete d
  simp only [ite_eq_right hs, ite_eq_right ht] at hv
  unfold eulerDefect
  by_cases hf : R.face.SameCycle d d.symm
  · have h := R.delete_face_count_same d hs ht hf
    right
    omega
  · have h := R.delete_face_count_different d ht hf
    left
    omega

theorem defect_delete_le : (R.deleteEdge d).eulerDefect ≤ R.eulerDefect := by
  by_cases hb : G.IsBridge d.edge
  · rw [R.bridge_defect d hb]
  · rcases R.nonbridge_defect d hb with h | h <;> omega

end JSP512Probe.RotationSystem
