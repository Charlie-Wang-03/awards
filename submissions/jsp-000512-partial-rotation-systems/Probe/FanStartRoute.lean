import Probe.FanStart
import Probe.FiniteFan

namespace JSP512Probe.RotationSystem
open EdgeInsertion CycleSurgery
variable {V : Type*} (G : SimpleGraph V)

/-- The initial spoke is oriented from the fresh center into the side graph. -/
def startAnchor (a : G.Dart) : (fanStartGraph G a).Dart :=
  ⟨(none, some a.fst), Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- Old side darts retain their ordered endpoints during initialization. -/
def startOldDart (a d : G.Dart) : (fanStartGraph G a).Dart :=
  ⟨(some d.fst, some d.snd), Or.inl d.adj⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (R : RotationSystem G)

/-- Rotation at the degree-one fresh center fixes its unique dart. -/
theorem startFan_rotate_anchor (a : G.Dart) :
    (startFan G R a).rotate (startAnchor G a) = startAnchor G a := by
  classical
  let E := dartEquiv (withIsolate G) (some a.fst) none (Option.some_ne_none _)
    (isolated_missing (withIsolate G) (isolateDarts G a) none (withIsolate_none_support G))
  change E ((pendantRotation (withIsolate G) (R.addIsolate) (isolateDarts G a))
    (E.symm (E none))) = E none
  rw [E.symm_apply_apply]
  rfl

/-- The first spoke exits onto the chosen old facial traversal. -/
theorem startFan_face_anchor (a : G.Dart) :
    (startFan G R a).face (startAnchor G a) = startOldDart G a (R.face a.symm) := by
  classical
  have hh := pendant_face_reverse (withIsolate G) (R.addIsolate) (isolateDarts G a)
    none (withIsolate_none_support G)
  dsimp only at hh
  have hr : (R.addIsolate).rotate (isolateDarts G a) = isolateDarts G (R.rotate a) :=
    addIsolate_face G R a.symm
  rw [hr] at hh
  change (startFan G R a).face (startAnchor G a) =
    startOldDart G a (R.rotate a) at hh
  exact hh

/-- Every old facial step away from the attachment corner is unchanged. -/
theorem startFan_face_old (a d : G.Dart) (hd : d ≠ a.symm) :
    (startFan G R a).face (startOldDart G a d) = startOldDart G a (R.face d) := by
  classical
  have hn : isolateDarts G d ≠ (isolateDarts G a).symm := by
    intro hh
    exact hd ((isolateDarts G).injective hh)
  have hh := pendant_face_old_away (withIsolate G) (R.addIsolate) (isolateDarts G a)
    none (withIsolate_none_support G) (isolateDarts G d) hn
  dsimp only at hh
  rw [addIsolate_face] at hh
  exact hh

/-- A side-face route with distinct targets avoiding the attachment vertex
becomes an actual valid fan route after fresh-center initialization. -/
theorem startFan_route (a : G.Dart) (ds : List G.Dart)
    (hr : FaceRoute R.face a.symm ds)
    (hd : ds.Pairwise (fun d e => d.snd ≠ e.snd))
    (ha : ∀ d ∈ ds, d.snd ≠ a.fst) :
    FanRoute (fanStartGraph G a) (startFan G R a) (startAnchor G a)
      (ds.map (startOldDart G a)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · apply FaceRoute.map_steps (startOldDart G a) ds a.symm
      ((startFan G R a).rotate (startAnchor G a)) hr
    · rw [startFan_rotate_anchor, startFan_face_anchor]
    · intro d hem
      exact startFan_face_old G R a d (fun hh => ha d hem (by rw [hh]; rfl))
  · apply List.pairwise_map.mpr
    exact hd.imp (fun h he => h (Option.some.inj he))
  · intro e he
    obtain ⟨d, hem, rfl⟩ := List.mem_map.mp he
    constructor
    · simp [startAnchor, startOldDart]
    · intro hh
      exact ha d hem ((fanStartGraph_center_adj G a d.snd).mp hh)

noncomputable local instance (H : SimpleGraph (Option V)) : DecidableRel H.Adj := Classical.decRel _

/-- Initialize and complete a whole fan directly from a side-face route.
Old adjacency is unchanged; the fresh center has exactly the requested neighbors. -/
theorem startFan_complete (a : G.Dart) (ds : List G.Dart)
    (hr : FaceRoute R.face a.symm ds)
    (hd : ds.Pairwise (fun d e => d.snd ≠ e.snd))
    (ha : ∀ d ∈ ds, d.snd ≠ a.fst) (hz : R.HasGenusZero) (hc : G.Connected) :
    ∃ K : SimpleGraph (Option V),
      (∀ u v, K.Adj (some u) (some v) ↔ G.Adj u v) ∧
      (∀ u, K.Adj none (some u) ↔ u = a.fst ∨ ∃ d ∈ ds, d.snd = u) ∧
      K.Connected ∧ ∃ T : RotationSystem K, T.HasGenusZero := by
  classical
  obtain ⟨K, hK, hconn, T, hT⟩ := EdgeInsertion.FanRoute.complete
    (fanStartGraph G a) (startFan G R a) (startAnchor G a)
    (ds.map (startOldDart G a)) (startFan_route G R a ds hr hd ha)
    (startFan_genusZero G R a hz) (fanStartGraph_connected G a hc)
  refine ⟨K, ?_, ?_, hconn, T, hT⟩
  · intro u v
    rw [hK]
    simp [startAnchor, fanStartGraph, addedGraph, withIsolate]
  · intro u
    rw [hK]
    have hmem : (∃ e ∈ ds.map (startOldDart G a), e.snd = some u) ↔
        ∃ d ∈ ds, d.snd = u := by
      constructor
      · rintro ⟨e, he, heu⟩
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        exact ⟨d, hd, Option.some.inj heu⟩
      · rintro ⟨d, hd, hdu⟩
        exact ⟨startOldDart G a d, List.mem_map.mpr ⟨d, hd, rfl⟩, congrArg some hdu⟩
    simp only [startAnchor, fanStartGraph, addedGraph, withIsolate,
      false_or, true_and, Option.some.injEq, Option.some_ne_none, and_false, false_and,
      or_false, eq_self]
    exact or_congr Iff.rfl hmem

end JSP512Probe.RotationSystem
