import Probe.FanContinuation

namespace JSP512Probe.EdgeInsertion
open RotationSystem CycleSurgery

/-- Successive darts along a facial traversal, excluding the starting dart. -/
def FaceRoute {α : Type*} (σ : α → α) (start : α) : List α → Prop
  | [] => True
  | d :: ds => σ start = d ∧ FaceRoute σ d ds

/-- A route transports even when its initial dart is replaced by a new spoke. -/
theorem FaceRoute.map_steps {α β : Type*} {σ : α → α} {τ : β → β}
    (f : α → β) (ds : List α) (s : α) (t : β)
    (hr : FaceRoute σ s ds) (hs : τ t = f (σ s))
    (hsteps : ∀ d ∈ ds, τ (f d) = f (σ d)) : FaceRoute τ t (ds.map f) := by
  induction ds generalizing s t with
  | nil => trivial
  | cons d ds ih =>
    obtain ⟨hd, ht⟩ := hr
    exact ⟨hs.trans (congrArg f hd), ih d (f d) ht (hsteps d (by simp))
      (fun e he => hsteps e (by simp [he]))⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (R : RotationSystem G)

/-- A finite boundary segment whose target vertices are distinct, different
from the center, and not yet joined to it. -/
structure FanRoute (a : G.Dart) (ds : List G.Dart) : Prop where
  route : FaceRoute R.face (R.rotate a) ds
  distinct : ds.Pairwise (fun d e => d.snd ≠ e.snd)
  missing : ∀ d ∈ ds, a.fst ≠ d.snd ∧ ¬G.Adj a.fst d.snd

/-- Removing the first route edge after inserting its spoke leaves a valid
route for all remaining insertions. -/
theorem FanRoute.tail (a d : G.Dart) (ds : List G.Dart)
    (h : FanRoute G R a (d :: ds)) :
    let hn := (h.missing d (by simp)).1
    let hm := (h.missing d (by simp)).2
    let S := addEdge G R a d.symm hn hm
    let E := dartEquiv G a.fst d.snd hn hm
    FanRoute (addedGraph G a.fst d.snd hn) S (E (some (some a)))
      (ds.map (fun e => E (some (some e)))) := by
  classical
  dsimp only
  let hn := (h.missing d (by simp)).1
  let hm := (h.missing d (by simp)).2
  let S := addEdge G R a d.symm hn hm
  let E := dartEquiv G a.fst d.snd hn hm
  let f := fun e : G.Dart => E (some (some e))
  have hd := (List.pairwise_cons.mp h.distinct).1
  have he : ∀ e ∈ ds, e ≠ a.symm ∧ e ≠ d := by
    intro e hem
    constructor
    · intro hh
      have he := (h.missing e (by simp [hem])).1
      exact he (by rw [hh]; rfl)
    · intro hh
      exact hd e hem (by rw [hh])
  refine ⟨?_, ?_, ?_⟩
  · apply FaceRoute.map_steps f ds d (S.rotate (f a)) h.route.2
    · exact added_next_path G R a d.symm hn hm
    · intro e hem
      exact added_face_old_away G R a d.symm hn hm e (he e hem).1 (he e hem).2
  · exact (List.pairwise_map.mpr (List.pairwise_cons.mp h.distinct).2)
  · intro e hem
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hem
    have hxold := h.missing x (by simp [hx])
    constructor
    · exact hxold.1
    · intro hh
      rcases hh with hh | hh | hh
      · exact hxold.2 hh
      · exact hd x hx hh.2.symm
      · exact hn hh.1

noncomputable local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _

/-- Every finite valid fan route can be completed. The final graph has exactly
the old edges and the requested spokes, and carries a zero-genus rotation. -/
theorem finite_fan_exists (n : ℕ) :
    ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (S : RotationSystem H)
      (a : H.Dart) (ds : List H.Dart), ds.length = n → FanRoute H S a ds →
      S.HasGenusZero → ∃ K : SimpleGraph V,
        (∀ u v, K.Adj u v ↔ H.Adj u v ∨
          (u = a.fst ∧ ∃ d ∈ ds, d.snd = v) ∨
          (v = a.fst ∧ ∃ d ∈ ds, d.snd = u)) ∧
        ∃ T : RotationSystem K, T.HasGenusZero := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H _ S a ds hlen hr hz
    cases ds with
    | nil =>
      refine ⟨H, ?_, S, hz⟩
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
      obtain ⟨K, hK, T, hT⟩ := ih (ds.map f).length hlt H' S' (f a) (ds.map f) rfl ht hz'
      refine ⟨K, ?_, T, hT⟩
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

/-- The completed fan is connected whenever the starting graph is connected. -/
theorem FanRoute.complete (a : G.Dart) (ds : List G.Dart)
    (hr : FanRoute G R a ds) (hz : R.HasGenusZero) (hc : G.Connected) :
    ∃ K : SimpleGraph V,
      (∀ u v, K.Adj u v ↔ G.Adj u v ∨
        (u = a.fst ∧ ∃ d ∈ ds, d.snd = v) ∨
        (v = a.fst ∧ ∃ d ∈ ds, d.snd = u)) ∧ K.Connected ∧
      ∃ T : RotationSystem K, T.HasGenusZero := by
  obtain ⟨K, hK, T, hT⟩ := finite_fan_exists ds.length G R a ds rfl hr hz
  exact ⟨K, hK, hc.mono (fun u v huv => (hK u v).mpr (Or.inl huv)), T, hT⟩

end JSP512Probe.EdgeInsertion
