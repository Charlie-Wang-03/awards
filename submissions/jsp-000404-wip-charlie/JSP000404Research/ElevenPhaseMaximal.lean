import JSP000404Research.ElevenPhaseData

namespace JSP000404Research.ElevenPhase

def occupied (r : Fin 11 → Option Bool) : Finset (Fin 11) :=
  Finset.univ.filter fun c ↦ (r c).isSome

theorem extends_self (r : Fin 11 → Option Bool) : Extends r r := by
  intro c b h
  exact h

theorem extends_update {r s : Fin 11 → Option Bool} (h : Extends r s)
    {c : Fin 11} (hc : s c = none) (b : Bool) :
    Extends r (Function.update s c (some b)) := by
  intro d bit hd
  by_cases hdc : d = c
  · subst d
    have he := h c bit hd
    simp [hc] at he
  · simpa [Function.update, hdc] using h d bit hd

theorem occupied_update {s : Fin 11 → Option Bool} {c : Fin 11}
    (hc : s c = none) (b : Bool) :
    (occupied (Function.update s c (some b))).card = (occupied s).card + 1 := by
  have hset : occupied (Function.update s c (some b)) = insert c (occupied s) := by
    ext d
    by_cases hdc : d = c
    · subst d
      simp [occupied]
    · simp [occupied, Function.update, hdc]
  have hnot : c ∉ occupied s := by simp [occupied, hc]
  rw [hset, Finset.card_insert_of_notMem hnot]

theorem exists_locally_maximal_extension (r : Fin 11 → Option Bool) (hr : LocalValid r) :
    ∃ s : Fin 11 → Option Bool, LocalValid s ∧ Extends r s ∧
      ∀ c, s c = none → ∀ b, ¬LocalValid (Function.update s c (some b)) := by
  classical
  let candidates : Finset (Fin 11 → Option Bool) :=
    Finset.univ.filter fun s ↦ LocalValid s ∧ Extends r s
  have hnonempty : candidates.Nonempty := ⟨r, by simp [candidates, hr, extends_self]⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image candidates (fun s ↦ (occupied s).card) hnonempty
  obtain ⟨hsvalid, hsextends⟩ := (Finset.mem_filter.mp hs).2
  refine ⟨s, hsvalid, hsextends, ?_⟩
  intro c hc b hb
  have hu : Function.update s c (some b) ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hb, extends_update hsextends hc b⟩
  have hm := hmax _ hu
  rw [occupied_update hc b] at hm
  omega

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem catalog_of_locally_maximal : ∀ r : Fin 11 → Option Bool, LocalValid r →
    (∀ c, r c = none → ∀ b, ¬LocalValid (Function.update r c (some b))) →
    ∃ i : Fin 198, Extends r (row i) := by
  decide +kernel

theorem catalog_completion (r : Fin 11 → Option Bool) (hr : LocalValid r) :
    ∃ i : Fin 198, Extends r (row i) := by
  obtain ⟨s, hs, hrs, hmax⟩ := exists_locally_maximal_extension r hr
  obtain ⟨i, hsi⟩ := catalog_of_locally_maximal s hs hmax
  exact ⟨i, fun c b h ↦ hsi c b (hrs c b h)⟩

#print axioms exists_locally_maximal_extension
#print axioms catalog_completion

end JSP000404Research.ElevenPhase
