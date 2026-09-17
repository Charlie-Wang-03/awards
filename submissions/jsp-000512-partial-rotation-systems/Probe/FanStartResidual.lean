import Probe.FanStartFaces
import Probe.ResidualFanVertices

namespace JSP512Probe.RotationSystem
open EdgeInsertion CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G)

/-- Residual simplicity transfers through initialization when the old
attachment occurrence is consumed by the route. -/
theorem startFan_residual_simple (a : G.Dart) (ds : List G.Dart)
    (hs : ResidualBoundarySimple G R a ds)
    (ha : ∀ d, R.face.SameCycle a.symm d → d ∉ ds → d.fst ≠ a.fst) :
    ResidualBoundarySimple (fanStartGraph G a) (startFan G R a) (startAnchor G a)
      (ds.map (startOldDart G a)) := by
  intro x y hx hy hnx hny hxy
  have old_not : ∀ d, startOldDart G a d ∉ ds.map (startOldDart G a) → d ∉ ds := by
    intro d hd hem
    exact hd (List.mem_map.mpr ⟨d, hem, rfl⟩)
  rcases startFan_dart_cases G a x with rfl | rfl | ⟨d, rfl⟩ <;>
    rcases startFan_dart_cases G a y with rfl | rfl | ⟨e, rfl⟩
  · rfl
  · cases hxy
  · cases hxy
  · cases hxy
  · rfl
  · exact False.elim (ha e ((startFan_outer_old_iff G R a e).mp hy)
      (old_not e hny) (Option.some.inj hxy).symm)
  · cases hxy
  · exact False.elim (ha d ((startFan_outer_old_iff G R a d).mp hx)
      (old_not d hnx) (Option.some.inj hxy))
  · have hde := hs d e ((startFan_outer_old_iff G R a d).mp hx)
      ((startFan_outer_old_iff G R a e).mp hy) (old_not d hnx) (old_not e hny)
      (Option.some.inj hxy)
    exact congrArg (startOldDart G a) hde

/-- The center is always on the residual initialized boundary; old vertices
are exactly the attachment vertex plus the old residual boundary vertices. -/
theorem startFan_residual_vertices (a : G.Dart) (ds : List G.Dart) (u : Option V) :
    ResidualBoundaryVertex (fanStartGraph G a) (startFan G R a) (startAnchor G a)
      (ds.map (startOldDart G a)) u ↔
    u = none ∨ u = some a.fst ∨ ∃ v, u = some v ∧ ResidualBoundaryVertex G R a ds v := by
  have old_mem : ∀ d, startOldDart G a d ∈ ds.map (startOldDart G a) ↔ d ∈ ds := by
    intro d
    constructor
    · intro hh
      obtain ⟨e, he, hed⟩ := List.mem_map.mp hh
      have hfst := Option.some.inj (congrArg (fun x : (fanStartGraph G a).Dart => x.fst) hed)
      have hsnd := Option.some.inj (congrArg (fun x : (fanStartGraph G a).Dart => x.snd) hed)
      have hde := SimpleGraph.Dart.ext e d (Prod.ext hfst hsnd)
      exact hde ▸ he
    · intro hh
      exact List.mem_map.mpr ⟨d, hh, rfl⟩
  have hanc : (startFan G R a).face.SameCycle (startAnchor G a).symm (startAnchor G a) := by
    have hh : (startFan G R a).face.SameCycle (startAnchor G a).symm
        ((startFan G R a).face (startAnchor G a).symm) := Equiv.Perm.SameCycle.rfl.apply_right
    rwa [startFan_face_forward] at hh
  constructor
  · rintro ⟨x, hx, hn, hxu⟩
    rcases startFan_dart_cases G a x with rfl | rfl | ⟨d, rfl⟩
    · exact Or.inl hxu.symm
    · exact Or.inr (Or.inl hxu.symm)
    · exact Or.inr (Or.inr ⟨d.fst, hxu.symm, d, (startFan_outer_old_iff G R a d).mp hx,
        fun h => hn ((old_mem d).mpr h), rfl⟩)
  · rintro (rfl | rfl | ⟨v, rfl, d, hd, hn, hdv⟩)
    · refine ⟨startAnchor G a, hanc, ?_, rfl⟩
      intro hh
      obtain ⟨e, _, he⟩ := List.mem_map.mp hh
      have hf := congrArg (fun x : (fanStartGraph G a).Dart => x.fst) he
      cases hf
    · refine ⟨(startAnchor G a).symm, Equiv.Perm.SameCycle.rfl, ?_, rfl⟩
      intro hh
      obtain ⟨e, _, he⟩ := List.mem_map.mp hh
      have ht := congrArg (fun x : (fanStartGraph G a).Dart => x.snd) he
      cases ht
    · exact ⟨startOldDart G a d, (startFan_outer_old_iff G R a d).mpr hd,
        fun h => hn ((old_mem d).mp h), congrArg some hdv⟩

end JSP512Probe.RotationSystem
