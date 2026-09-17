import Probe.FanStartResidual
import Probe.TriangulatedFan

namespace JSP512Probe.RotationSystem
open EdgeInsertion CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G)
noncomputable local instance (H : SimpleGraph (Option V)) : DecidableRel H.Adj := Classical.decRel _

/-- Restore a whole fresh-center fan as an actual triangulated disk, with exact
old edges, exact center neighbors, and exact final boundary vertices. -/
theorem startFan_disk_edges (a : G.Dart) (ds : List G.Dart)
    (hr : FaceRoute R.face a.symm ds)
    (hd : ds.Pairwise (fun d e => d.snd ≠ e.snd))
    (ha : ∀ d ∈ ds, d.snd ≠ a.fst) (hz : R.HasGenusZero) (hc : G.Connected)
    (hi : ∀ d, ¬R.face.SameCycle a.symm d → R.face (R.face (R.face d)) = d)
    (hs : ResidualBoundarySimple G R a ds)
    (hattach : ∀ d, R.face.SameCycle a.symm d → d ∉ ds → d.fst ≠ a.fst) :
    ∃ K : SimpleGraph (Option V),
      (∀ u v, K.Adj (some u) (some v) ↔ G.Adj u v) ∧
      (∀ u, K.Adj none (some u) ↔ u = a.fst ∨ ∃ d ∈ ds, d.snd = u) ∧
      ∃ T : RotationSystem K, ∃ c : K.Dart,
        c.toProd = (none, some a.fst) ∧ T.IsTriangulatedDisk c.symm ∧
        (∀ u, u ∈ T.facialVertices c.symm ↔
          u = none ∨ u = some a.fst ∨ ∃ v, u = some v ∧ ResidualBoundaryVertex G R a ds v) ∧
        ∀ d : G.Dart, R.face.SameCycle a.symm d → d ∉ ds →
          ∃ e : K.Dart, e.toProd = (some d.fst,some d.snd) ∧ T.face.SameCycle c.symm e := by
  classical
  obtain ⟨K, hK, T, c, hca, hD, hverts, hedge⟩ := EdgeInsertion.FanRoute.complete_disk_of_residual_edges
    (fanStartGraph G a) (startFan G R a) (startAnchor G a)
    (ds.map (startOldDart G a)) (startFan_route G R a ds hr hd ha)
    (startFan_genusZero G R a hz) (fanStartGraph_connected G a hc)
    (startFan_inner G R a hi) (startFan_residual_simple G R a ds hs hattach)
  refine ⟨K, ?_, ?_, T, c, hca, hD,
    fun u => (hverts u).trans (startFan_residual_vertices G R a ds u),?_⟩
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
  · intro d houter hnot
    apply hedge (startOldDart G a d)
    · exact (startFan_outer_old_iff G R a d).mpr houter
    · intro hm
      obtain ⟨w,hw,he⟩ := List.mem_map.mp hm
      have hwd : w = d := by
        apply SimpleGraph.Dart.ext
        apply Prod.ext
        · exact Option.some.inj (congrArg (fun z => z.fst) he)
        · exact Option.some.inj (congrArg (fun z => z.snd) he)
      exact hnot (hwd ▸ hw)
    · change some d.fst ≠ none
      simp

/-- Compatibility projection retaining the original disk-and-vertices interface. -/
theorem startFan_disk (a : G.Dart) (ds : List G.Dart)
    (hr : FaceRoute R.face a.symm ds)
    (hd : ds.Pairwise (fun d e => d.snd ≠ e.snd))
    (ha : ∀ d ∈ ds, d.snd ≠ a.fst) (hz : R.HasGenusZero) (hc : G.Connected)
    (hi : ∀ d, ¬R.face.SameCycle a.symm d → R.face (R.face (R.face d)) = d)
    (hs : ResidualBoundarySimple G R a ds)
    (hattach : ∀ d, R.face.SameCycle a.symm d → d ∉ ds → d.fst ≠ a.fst) :
    ∃ K : SimpleGraph (Option V),
      (∀ u v, K.Adj (some u) (some v) ↔ G.Adj u v) ∧
      (∀ u, K.Adj none (some u) ↔ u = a.fst ∨ ∃ d ∈ ds, d.snd = u) ∧
      ∃ T : RotationSystem K, ∃ c : K.Dart,
        c.toProd = (none, some a.fst) ∧ T.IsTriangulatedDisk c.symm ∧
        ∀ u, u ∈ T.facialVertices c.symm ↔
          u = none ∨ u = some a.fst ∨ ∃ v, u = some v ∧ ResidualBoundaryVertex G R a ds v := by
  obtain ⟨K,hK,hcenter,T,c,hca,hD,hverts,_⟩ :=
    startFan_disk_edges G R a ds hr hd ha hz hc hi hs hattach
  exact ⟨K,hK,hcenter,T,c,hca,hD,hverts⟩

end JSP512Probe.RotationSystem
