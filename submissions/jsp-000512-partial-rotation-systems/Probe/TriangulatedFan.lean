import Probe.FiniteFan
import Probe.ResidualFanVertices
import Probe.DiskInstance

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _

/-- Completing a finite fan preserves all inner triangles, with the same
oriented boundary anchor and exactly the requested additional spokes. -/
theorem triangulated_fan_exists_edges (n : ℕ) :
    ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (S : RotationSystem H)
      (a : H.Dart) (ds : List H.Dart), ds.length = n → FanRoute H S a ds →
      S.HasGenusZero →
      (∀ d, ¬S.face.SameCycle a.symm d → S.face (S.face (S.face d)) = d) → ∃ K : SimpleGraph V,
        (∀ u v, K.Adj u v ↔ H.Adj u v ∨
          (u = a.fst ∧ ∃ d ∈ ds, d.snd = v) ∨
          (v = a.fst ∧ ∃ d ∈ ds, d.snd = u)) ∧
        ∃ T : RotationSystem K, T.HasGenusZero ∧ ∃ c : K.Dart,
          c.toProd = a.toProd ∧
          (∀ d, ¬T.face.SameCycle c.symm d → T.face (T.face (T.face d)) = d) ∧
          (∀ u, ResidualBoundaryVertex K T c [] u ↔ ResidualBoundaryVertex H S a ds u) ∧
          (ResidualBoundarySimple H S a ds →
            ∀ x y, T.face.SameCycle c.symm x → T.face.SameCycle c.symm y → x.fst = y.fst → x = y) ∧
          (∀ d : H.Dart, S.face.SameCycle a.symm d → d ∉ ds → d.fst ≠ a.fst →
            ∃ e : K.Dart, e.toProd = d.toProd ∧ T.face.SameCycle c.symm e) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H _ S a ds hlen hr hz hinner
    cases ds with
    | nil =>
      refine ⟨H, ?_, S, hz, a, rfl, hinner, fun _ => Iff.rfl, fun hs x y hx hy he => hs x y hx hy (by simp) (by simp) he,
        fun d hd _ _ => ⟨d,rfl,hd⟩⟩
      intro u v
      simp
    | cons d ds =>
      let hn := (hr.missing d (by simp)).1
      let hm := (hr.missing d (by simp)).2
      let H' := addedGraph H a.fst d.snd hn
      let S' := addEdge H S a d.symm hn hm
      let E := dartEquiv H a.fst d.snd hn hm
      let f := fun e : H.Dart => E (some (some e))
      have ht : FanRoute H' S' (f a) (ds.map f) := hr.tail H S a d ds
      have hz' : S'.HasGenusZero := added_ear_genusZero H S a d.symm hn hm hr.route.1 hz
      have hlt : (ds.map f).length < n := by
        simp only [List.length_map]
        simp only [List.length_cons] at hlen
        omega
      have hinner' : ∀ e, ¬S'.face.SameCycle (f a).symm e →
          S'.face (S'.face (S'.face e)) = e :=
        added_inner_triangles H S a d.symm hn hm hr.route.1 hinner
      obtain ⟨K, hK, T, hT, c, hc, hi, hverts, hsimp, hedge⟩ :=
        ih (ds.map f).length hlt H' S' (f a) (ds.map f) rfl ht hz' hinner'
      have kept : ∀ z : H.Dart, S.face.SameCycle a.symm z → z ∉ d :: ds →
          z.fst ≠ a.fst → ∃ e : K.Dart, e.toProd = z.toProd ∧ T.face.SameCycle c.symm e := by
        intro z hzo hzn hza
        have hrot : z ≠ S.rotate a := by
          intro he
          exact hza ((congrArg (fun x : H.Dart => x.fst) he).trans (S.source a))
        have hzd : z ≠ d := fun he => hzn (by simp [he])
        have ho : S'.face.SameCycle (f a).symm (f z) := by
          apply (added_outer_old_iff H S a d.symm hn hm hr.route.1 z).mpr
          exact ⟨hzo,hrot,by simpa only [SimpleGraph.Dart.symm_symm] using hzd⟩
        have hnot : f z ∉ ds.map f := by
          intro hmem
          obtain ⟨w,hw,he⟩ := List.mem_map.mp hmem
          have heq : w = z := Option.some.inj (Option.some.inj (E.injective he))
          exact hzn (List.mem_cons_of_mem _ (heq ▸ hw))
        exact hedge (f z) ho hnot hza
      refine ⟨K, ?_, T, hT, c, hc, hi,
        fun u => (hverts u).trans (hr.residual_vertices_tail H S a d ds u),
        fun hs => hsimp (hr.residual_simple_tail H S a d ds hs),kept⟩
      intro u v
      rw [hK]
      change (H.Adj u v ∨ (u = a.fst ∧ v = d.snd) ∨ (u = d.snd ∧ v = a.fst)) ∨
        (u = a.fst ∧ ∃ e ∈ ds.map f, e.snd = v) ∨
        (v = a.fst ∧ ∃ e ∈ ds.map f, e.snd = u) ↔ _
      have hmemb : ∀ w, (∃ e ∈ ds.map f, e.snd = w) ↔ ∃ e ∈ ds, e.snd = w := by
        intro w
        simp only [List.mem_map]
        constructor
        · rintro ⟨e, ⟨x, hx, rfl⟩, he⟩
          exact ⟨x, hx, he⟩
        · rintro ⟨e, he, hw⟩
          exact ⟨f e, ⟨e, he, rfl⟩, hw⟩
      rw [hmemb, hmemb]
      simp only [List.mem_cons, exists_eq_or_imp]
      have hv : (v = d.snd) ↔ d.snd = v := eq_comm
      have hu : (u = d.snd) ↔ d.snd = u := eq_comm
      rw [hv, hu]
      constructor
      · rintro ((hh | ⟨hu, hv⟩ | ⟨hu, hv⟩) | ⟨hu, hh⟩ | ⟨hv, hh⟩)
        · exact Or.inl hh
        · exact Or.inr (Or.inl ⟨hu, Or.inl hv⟩)
        · exact Or.inr (Or.inr ⟨hv, Or.inl hu⟩)
        · exact Or.inr (Or.inl ⟨hu, Or.inr hh⟩)
        · exact Or.inr (Or.inr ⟨hv, Or.inr hh⟩)
      · rintro (hh | ⟨hu, hv | hh⟩ | ⟨hv, hu | hh⟩)
        · exact Or.inl (Or.inl hh)
        · exact Or.inl (Or.inr (Or.inl ⟨hu, hv⟩))
        · exact Or.inr (Or.inl ⟨hu, hh⟩)
        · exact Or.inl (Or.inr (Or.inr ⟨hu, hv⟩))
        · exact Or.inr (Or.inr ⟨hv, hh⟩)


/-- Compatibility projection of finite fan completion with edge preservation. -/
theorem triangulated_fan_exists (n : ℕ) :
    ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (S : RotationSystem H)
      (a : H.Dart) (ds : List H.Dart), ds.length = n → FanRoute H S a ds →
      S.HasGenusZero →
      (∀ d, ¬S.face.SameCycle a.symm d → S.face (S.face (S.face d)) = d) → ∃ K : SimpleGraph V,
        (∀ u v, K.Adj u v ↔ H.Adj u v ∨
          (u = a.fst ∧ ∃ d ∈ ds, d.snd = v) ∨
          (v = a.fst ∧ ∃ d ∈ ds, d.snd = u)) ∧
        ∃ T : RotationSystem K, T.HasGenusZero ∧ ∃ c : K.Dart,
          c.toProd = a.toProd ∧
          (∀ d, ¬T.face.SameCycle c.symm d → T.face (T.face (T.face d)) = d) ∧
          (∀ u, ResidualBoundaryVertex K T c [] u ↔ ResidualBoundaryVertex H S a ds u) ∧
          (ResidualBoundarySimple H S a ds →
            ∀ x y, T.face.SameCycle c.symm x → T.face.SameCycle c.symm y → x.fst = y.fst → x = y) := by
  intro H _ S a ds hlen hr hz hi
  obtain ⟨K,hK,T,hT,c,hc,hinner,hverts,hsimple,_⟩ :=
    triangulated_fan_exists_edges n H S a ds hlen hr hz hi
  exact ⟨K,hK,T,hT,c,hc,hinner,hverts,hsimple⟩

/-- Connected finite fan completion with all non-outer faces triangular.
Outer-face simplicity is deliberately not assumed or concluded here. -/
theorem FanRoute.complete_with_inner_faces (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : RotationSystem G) (a : G.Dart) (ds : List G.Dart)
    (hr : FanRoute G R a ds) (hz : R.HasGenusZero) (hc : G.Connected)
    (hi : ∀ d, ¬R.face.SameCycle a.symm d → R.face (R.face (R.face d)) = d) :
    ∃ K : SimpleGraph V,
      (∀ u v, K.Adj u v ↔ G.Adj u v ∨
        (u = a.fst ∧ ∃ d ∈ ds, d.snd = v) ∨
        (v = a.fst ∧ ∃ d ∈ ds, d.snd = u)) ∧ K.Connected ∧
      ∃ T : RotationSystem K, T.HasGenusZero ∧ ∃ c : K.Dart,
        c.toProd = a.toProd ∧ ∀ d, ¬T.face.SameCycle c.symm d →
          T.face (T.face (T.face d)) = d := by
  obtain ⟨K, hK, T, hzT, c, hca, hinner, _, _⟩ :=
    triangulated_fan_exists ds.length G R a ds rfl hr hz hi
  exact ⟨K, hK, hc.mono (fun u v huv => (hK u v).mpr (Or.inl huv)),
    T, hzT, c, hca, hinner⟩

/-- A valid finite fan route in a triangulated disk yields a triangulated disk
with exactly the requested extra spokes and the original oriented anchor. -/
theorem FanRoute.complete_disk (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : RotationSystem G) (a : G.Dart) (ds : List G.Dart)
    (hr : FanRoute G R a ds) (hD : R.IsTriangulatedDisk a.symm) :
    ∃ K : SimpleGraph V,
      (∀ u v, K.Adj u v ↔ G.Adj u v ∨
        (u = a.fst ∧ ∃ d ∈ ds, d.snd = v) ∨
        (v = a.fst ∧ ∃ d ∈ ds, d.snd = u)) ∧
      ∃ T : RotationSystem K, ∃ c : K.Dart,
        c.toProd = a.toProd ∧ T.IsTriangulatedDisk c.symm := by
  obtain ⟨K, hK, T, hzT, c, hca, hinner, hverts, hsimple⟩ :=
    triangulated_fan_exists ds.length G R a ds rfl hr hD.zero hD.inner
  exact ⟨K, hK, T, c, hca, hzT,
    hD.connected.mono (fun u v huv => (hK u v).mpr (Or.inl huv)),
    hsimple (fun x y hx hy _ _ he => hD.simple x y hx hy he), hinner⟩

/-- Repeated vertices on the initial outer face are allowed if all duplicate
occurrences disappear along the route. Only the retained part must be simple. -/
theorem FanRoute.complete_disk_of_residual_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : RotationSystem G) (a : G.Dart) (ds : List G.Dart)
    (hr : FanRoute G R a ds) (hz : R.HasGenusZero) (hc : G.Connected)
    (hi : ∀ d, ¬R.face.SameCycle a.symm d → R.face (R.face (R.face d)) = d)
    (hs : ResidualBoundarySimple G R a ds) :
    ∃ K : SimpleGraph V,
      (∀ u v, K.Adj u v ↔ G.Adj u v ∨
        (u = a.fst ∧ ∃ d ∈ ds, d.snd = v) ∨
        (v = a.fst ∧ ∃ d ∈ ds, d.snd = u)) ∧
      ∃ T : RotationSystem K, ∃ c : K.Dart,
        c.toProd = a.toProd ∧ T.IsTriangulatedDisk c.symm ∧
        (∀ u, u ∈ T.facialVertices c.symm ↔ ResidualBoundaryVertex G R a ds u) ∧
        ∀ d : G.Dart, R.face.SameCycle a.symm d → d ∉ ds → d.fst ≠ a.fst →
          ∃ e : K.Dart, e.toProd = d.toProd ∧ T.face.SameCycle c.symm e := by
  obtain ⟨K, hK, T, hzT, c, hca, hinner, hverts, hsimple, hedge⟩ :=
    triangulated_fan_exists_edges ds.length G R a ds rfl hr hz hi
  refine ⟨K, hK, T, c, hca, ⟨hzT,
    hc.mono (fun u v huv => (hK u v).mpr (Or.inl huv)), hsimple hs, hinner⟩, ?_,hedge⟩
  intro u
  simpa only [ResidualBoundaryVertex, RotationSystem.facialVertices, Set.mem_ofPred_eq,
    List.not_mem_nil, not_false_eq_true, true_and] using hverts u

/-- Compatibility projection of residual disk completion with old edges. -/
theorem FanRoute.complete_disk_of_residual (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : RotationSystem G) (a : G.Dart) (ds : List G.Dart)
    (hr : FanRoute G R a ds) (hz : R.HasGenusZero) (hc : G.Connected)
    (hi : ∀ d, ¬R.face.SameCycle a.symm d → R.face (R.face (R.face d)) = d)
    (hs : ResidualBoundarySimple G R a ds) :
    ∃ K : SimpleGraph V,
      (∀ u v, K.Adj u v ↔ G.Adj u v ∨
        (u = a.fst ∧ ∃ d ∈ ds, d.snd = v) ∨
        (v = a.fst ∧ ∃ d ∈ ds, d.snd = u)) ∧
      ∃ T : RotationSystem K, ∃ c : K.Dart,
        c.toProd = a.toProd ∧ T.IsTriangulatedDisk c.symm ∧
        ∀ u, u ∈ T.facialVertices c.symm ↔ ResidualBoundaryVertex G R a ds u := by
  obtain ⟨K,hK,T,c,hca,hD,hverts,_⟩ :=
    hr.complete_disk_of_residual_edges G R a ds hz hc hi hs
  exact ⟨K,hK,T,c,hca,hD,hverts⟩

end JSP512Probe.EdgeInsertion
