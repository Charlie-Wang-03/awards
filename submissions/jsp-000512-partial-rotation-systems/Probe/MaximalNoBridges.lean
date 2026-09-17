import Probe.MaximalConnectivity

namespace JSP512Probe.RotationSystem
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : RotationSystem G)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A component with singleton rotations at both ends of an edge contains
only those two endpoints. -/
theorem reachable_of_endpoints_fixed (d : G.Dart)
    (hs : R.rotate d = d) (ht : R.rotate d.symm = d.symm)
    {x : V} (hx : G.Reachable d.fst x) : x = d.fst ∨ x = d.snd := by
  have closed : ∀ u v, G.Adj u v → (u = d.fst ∨ u = d.snd) →
      v = d.fst ∨ v = d.snd := by
    intro u v ha hu
    rcases hu with rfl | rfl
    · have he := (R.rotate_fixed_iff_unique d).mp hs ⟨(d.fst,v),ha⟩ rfl
      exact Or.inr (congrArg (fun e : G.Dart => e.snd) he)
    · have he := (R.rotate_fixed_iff_unique d.symm).mp ht ⟨(d.snd,v),ha⟩ rfl
      exact Or.inl (congrArg (fun e : G.Dart => e.snd) he)
  have inv : ∀ {u v}, G.Walk u v → (u = d.fst ∨ u = d.snd) →
      v = d.fst ∨ v = d.snd := by
    intro u v p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hu => ih (closed _ _ h hu)
  obtain ⟨p⟩ := hx
  exact inv p (Or.inl rfl)

/-- Any bridge in a maximal genus-zero graph forces exactly two vertices. -/
theorem maximal_bridge_card (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (d : G.Dart) (hb : G.IsBridge d.edge) :
    Fintype.card V = 2 := by
  classical
  have hc := R.maximal_connected_of_dart hz hmax d
  obtain ⟨hs,ht⟩ := R.maximal_bridge_endpoints_fixed hz hmax d hb
  have hu : (Finset.univ : Finset V) = {d.fst,d.snd} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact R.reachable_of_endpoints_fixed d hs ht (hc d.fst x)
  have hh := congrArg Finset.card hu
  simpa [d.fst_ne_snd] using hh

/-- At least three vertices exclude all bridges in a maximal genus-zero graph. -/
theorem maximal_not_bridge (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (d : G.Dart) :
    ¬G.IsBridge d.edge := by
  intro hb
  have hh := R.maximal_bridge_card hz hmax d hb
  omega

/-- The two orientations of every edge belong to different faces. -/
theorem maximal_edge_distinct_faces (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (d : G.Dart) :
    ¬R.face.SameCycle d d.symm := by
  exact R.genusZero_nonbridge_faces hz d (R.maximal_not_bridge hz hmax hn d)

/-- No face contains both orientations of any edge. This is edge simplicity,
not yet absence of repeated vertices in the facial walk. -/
theorem maximal_face_edge_injective (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V)
    (x y : G.Dart) (hf : R.face.SameCycle x y) (he : x.edge = y.edge) : x = y := by
  rcases (SimpleGraph.dart_edge_eq_iff x y).mp he with h | h
  · exact h
  · have hy : y = x.symm := by simpa using congrArg SimpleGraph.Dart.symm h.symm
    rw [hy] at hf
    exact False.elim (R.maximal_edge_distinct_faces hz hmax hn x hf)

/-- Facial walks cannot close after only two steps. -/
theorem maximal_face_two_steps_ne (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (d : G.Dart) :
    R.face (R.face d) ≠ d := by
  intro hh
  have ht : (R.face d).snd = d.fst := by
    rw [← R.face_source (R.face d), hh]
  have he : R.face d = d.symm :=
    SimpleGraph.Dart.ext _ _ (Prod.ext (R.face_source d) ht)
  apply R.maximal_edge_distinct_faces hz hmax hn d
  rw [← he]
  exact Equiv.Perm.SameCycle.rfl.apply_right

/-- Every endpoint has another outgoing dart when there are at least three vertices. -/
theorem maximal_rotations_nonfixed (hz : R.HasGenusZero)
    (hmax : EdgeMaximalGenusZero G) (hn : 3 ≤ Fintype.card V) (d : G.Dart) :
    R.rotate d ≠ d ∧ R.rotate d.symm ≠ d.symm :=
  R.nonbridge_rotations d (R.maximal_not_bridge hz hmax hn d)

end JSP512Probe.RotationSystem
