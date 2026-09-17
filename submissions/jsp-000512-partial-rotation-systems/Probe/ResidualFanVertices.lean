import Probe.ResidualFanBoundary

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G)

/-- Vertices occurring on the part of the outer face not consumed by a route. -/
def ResidualBoundaryVertex (a : G.Dart) (ds : List G.Dart) (u : V) : Prop :=
  ∃ x, R.face.SameCycle a.symm x ∧ x ∉ ds ∧ x.fst = u

/-- One insertion preserves exactly the vertices of the eventual residual
boundary, even if the original outer face repeats vertices. -/
theorem FanRoute.residual_vertices_tail (a d : G.Dart) (ds : List G.Dart)
    (hr : FanRoute G R a (d :: ds)) (u : V) :
    let hn := (hr.missing d (by simp)).1
    let hm := (hr.missing d (by simp)).2
    let S := addEdge G R a d.symm hn hm
    let E := dartEquiv G a.fst d.snd hn hm
    ResidualBoundaryVertex (addedGraph G a.fst d.snd hn) S (E (some (some a)))
      (ds.map (fun e => E (some (some e)))) u ↔ ResidualBoundaryVertex G R a (d :: ds) u := by
  classical
  dsimp only
  let hn := (hr.missing d (by simp)).1
  let hm := (hr.missing d (by simp)).2
  let S := addEdge G R a d.symm hn hm
  let E := dartEquiv G a.fst d.snd hn hm
  let f := fun e : G.Dart => E (some (some e))
  constructor
  · rintro ⟨x, hx, hnx, hxu⟩
    obtain ⟨w, hw, hwd, hxw, hrep⟩ :=
      added_outer_representative G R a d.symm hn hm hr.route.1 x hx
    refine ⟨w, hw, ?_, hxw.symm.trans hxu⟩
    intro hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hwd rfl
    · by_cases he : w = R.rotate a
      · subst w
        exact hr.first_spoke_not_mem G R a (d :: ds) (by simp [hmem])
      · apply hnx
        rw [hrep, ite_eq_right he]
        exact List.mem_map.mpr ⟨w, hmem, rfl⟩
  · rintro ⟨w, hw, hnot, hwu⟩
    by_cases he : w = R.rotate a
    · subst w
      refine ⟨E (some none), ?_, ?_, (R.source a).symm.trans hwu⟩
      · have hh : S.face.SameCycle (E (some (some a.symm)))
            (S.face (E (some (some a.symm)))) := Equiv.Perm.SameCycle.rfl.apply_right
        have hf : S.face (E (some (some a.symm))) = E (some none) :=
          added_face_left G R a d.symm hn hm
        rw [hf] at hh
        exact hh
      · intro hmem
        obtain ⟨e, _, hh⟩ := List.mem_map.mp hmem
        have hi := E.injective hh
        simp at hi
    · refine ⟨f w, ?_, ?_, hwu⟩
      · apply (added_outer_old_iff G R a d.symm hn hm hr.route.1 w).mpr
        exact ⟨hw, he, fun hh => hnot (by simp [hh])⟩
      · intro hmem
        obtain ⟨e, hem, hh⟩ := List.mem_map.mp hmem
        have hew : e = w := Option.some.inj (Option.some.inj (E.injective hh))
        subst e
        exact hnot (by simp [hem])

end JSP512Probe.EdgeInsertion
