import JSP000404Research.OneMissingHansel
import Mathlib.Tactic

/-!
# At most one fully specified vertex still saves one Boolean bit

On n+1 Boolean coordinates, weighted Hansel gives

  sum_v 2^((n+1) - card(specified v)) <= 2^(n+1).

A fully specified vertex contributes exactly 1. Every non-full vertex
contributes at least 2. Hence if there is at most one fully specified vertex,

  2 * |V| - 1 <= 2^(n+1),

which, by integrality, implies

  |V| <= 2^n.

This weakens the geometric target in OneMissingHansel: a phase need not make
every vertex miss a standard direction band; one exceptional full vertex is
harmless.
-/

namespace JSP000404Research

open scoped BigOperators

/-- At most one full partial word on n+1 coordinates gives cardinality at most
2^n. -/
theorem hansel_card_le_two_pow_of_atMostOne_full
    {V : Type*} [Fintype V] {n : ℕ}
    (bit : V → Fin (n + 1) → Bool)
    (specified : V → Finset (Fin (n + 1)))
    (hsep : ∀ v w, v ≠ w → ∃ i,
      i ∈ specified v ∧ i ∈ specified w ∧ bit v i ≠ bit w i)
    (hfull : ∀ v w,
      specified v = Finset.univ →
      specified w = Finset.univ →
      v = w) :
    Fintype.card V ≤ 2 ^ n := by
  classical
  by_cases hex : ∃ v, specified v = Finset.univ
  · obtain ⟨v0, hv0⟩ := hex
    let term : V → ℕ :=
      fun v => 2 ^ ((n + 1) - (specified v).card)
    have hmissing :
        ∀ v ∈ (Finset.univ.erase v0), specified v ≠ Finset.univ := by
      intro v hv hcontra
      have hv_eq : v = v0 := hfull v v0 hcontra hv0
      subst v
      exact (Finset.not_mem_erase v0 Finset.univ) hv
    have hterm :
        ∀ v ∈ (Finset.univ.erase v0), 2 ≤ term v := by
      intro v hv
      have hne := hmissing v hv
      have hcard_lt : (specified v).card < n + 1 := by
        have hcard_le : (specified v).card ≤ n + 1 := by
          have h :=
            Finset.card_le_card (Finset.subset_univ (specified v))
          simpa using h
        by_contra hnot
        have heq : (specified v).card = n + 1 := by omega
        apply hne
        apply Finset.eq_univ_of_card
        simpa using heq
      have hexp : 1 ≤ (n + 1) - (specified v).card := by omega
      dsimp [term]
      calc
        2 = 2 ^ (1 : ℕ) := by norm_num
        _ ≤ 2 ^ ((n + 1) - (specified v).card) :=
          Nat.pow_le_pow_right (by decide) hexp
    have herase :
        (Finset.univ.erase v0).card * 2 ≤
          ∑ v ∈ (Finset.univ.erase v0), term v := by
      have hs :
          (∑ _v ∈ (Finset.univ.erase v0), 2) ≤
            ∑ v ∈ (Finset.univ.erase v0), term v :=
        Finset.sum_le_sum fun v hv => hterm v hv
      simpa [Nat.mul_comm] using hs
    have hterm0 : term v0 = 1 := by
      dsimp [term]
      rw [hv0]
      simp
    have hweighted :
        (∑ v : V, term v) ≤ 2 ^ (n + 1) := by
      dsimp [term]
      exact weighted_hansel bit specified hsep
    have hsplit :
        (∑ v : V, term v) =
          (∑ v ∈ (Finset.univ.erase v0), term v) + term v0 := by
      rw [← Finset.sum_erase_add (Finset.univ) term (Finset.mem_univ v0)]
      rfl
    have hcardpos : 1 ≤ Fintype.card V := by
      exact Fintype.card_pos_iff.mpr ⟨v0⟩
    have hcarderase :
        (Finset.univ.erase v0).card = Fintype.card V - 1 := by
      simp
    have hlower :
        (Fintype.card V - 1) * 2 + 1 ≤ 2 ^ (n + 1) := by
      rw [hsplit, hterm0] at hweighted
      rw [hcarderase] at herase
      omega
    rw [pow_succ] at hlower
    omega
  · apply hansel_card_le_two_pow_of_every_vertex_missing
      bit specified hsep
    intro v hv
    exact hex ⟨v, hv⟩

/-- Direction-band specialization. -/
theorem unitBand_card_le_two_pow_of_atMostOne_full
    {V : Type*} [LinearOrder V] [Fintype V]
    {width : ℝ}
    (D : DirectionData V width) (n : ℕ)
    (hwidth : width ≤ (n + 1 : ℕ))
    (hfull : ∀ v w,
      DirectionData.incidentBands D (n + 1) v = Finset.univ →
      DirectionData.incidentBands D (n + 1) w = Finset.univ →
      v = w) :
    Fintype.card V ≤ 2 ^ n := by
  exact hansel_card_le_two_pow_of_atMostOne_full
    (DirectionData.bandBit D (n + 1))
    (DirectionData.incidentBands D (n + 1))
    (DirectionData.unitBand_separates D (n + 1) hwidth)
    hfull

#print axioms hansel_card_le_two_pow_of_atMostOne_full
#print axioms unitBand_card_le_two_pow_of_atMostOne_full

end JSP000404Research
