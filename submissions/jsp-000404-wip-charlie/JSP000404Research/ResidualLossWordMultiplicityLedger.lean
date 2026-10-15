import JSP000404Research.ResidualLossDuplicateDebtLedger
import Mathlib.Tactic

/-!
# Word-centric exact multiplicity ledger of projected loss collisions

Prior certificates enumerate duplicate debt by coordinate slices and
actual retained-edge carrier events. Here each Boolean word itself is
charged exactly as many times as its translated-loss slice multiplicity
exceeds one.

Ddup = Σ_{word in U} (mult(word) - 1).

This provides an exact, compact formulation of the GLOBAL reuse defect
and exposes which Boolean words need simultaneous non-reusing payment.
It does not assert that any such word is an outside true hole or that
AngleCap enforces a matching into spare resources.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Number of different chosen flip-coordinate slices containing
the SAME concrete Boolean word. -/
noncomputable def lossWordMultiplicity
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (word : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter
    (fun c => word ∈ translatedLossSliceWords C exponent choice c)).card

/-- A word is included in the actual translated-loss union
iff its slice multiplicity is positive. -/
theorem lossWordMultiplicity_pos_iff_mem_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n)
    (word : Fin n → Bool) :
    0 < lossWordMultiplicity C exponent choice word ↔
      word ∈ translatedLossAllCoordinateWords C exponent choice := by
  classical
  unfold lossWordMultiplicity translatedLossAllCoordinateWords
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hp
    exact Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_univ c, (Finset.mem_filter.mp hc).2⟩
  · intro hw
    obtain ⟨c, hc, hword⟩ := Finset.mem_biUnion.mp hw
    apply Finset.card_pos.mpr
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hword⟩⟩

/-- Exact incidence double counting between concrete Boolean words
and the set of chosen flip-coordinate slices that contain each word. -/
theorem lossCoordinateSlice_card_sum_eq_wordMultiplicity_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    (∑ c : Fin n,
      (translatedLossSliceWords C exponent choice c).card) =
      ∑ word ∈ translatedLossAllCoordinateWords C exponent choice,
        lossWordMultiplicity C exponent choice word := by
  classical
  have hdouble :=
    Finset.sum_card_eq_sum_biUnion_card
      (fun c : Fin n => translatedLossSliceWords C exponent choice c)
      (Finset.univ : Finset (Fin n))
  simpa [translatedLossAllCoordinateWords, lossWordMultiplicity] using hdouble

/-- Every Boolean word in the union contributes one essential count
and exactly (slice multiplicity - 1) duplicate counts. -/
theorem lossWordMultiplicity_sum_eq_duplicate_plus_union
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    (∑ word ∈ translatedLossAllCoordinateWords C exponent choice,
      lossWordMultiplicity C exponent choice word) =
      (∑ word ∈ translatedLossAllCoordinateWords C exponent choice,
        lossWordMultiplicity C exponent choice word - 1) +
        (translatedLossAllCoordinateWords C exponent choice).card := by
  classical
  let U := translatedLossAllCoordinateWords C exponent choice
  have hpoint : ∀ word ∈ U,
      lossWordMultiplicity C exponent choice word =
        (lossWordMultiplicity C exponent choice word - 1) + 1 := by
    intro word hw
    have hp :=
      (lossWordMultiplicity_pos_iff_mem_union
        C exponent choice word).2 hw
    omega
  change (∑ word ∈ U, lossWordMultiplicity C exponent choice word) =
    (∑ word ∈ U, lossWordMultiplicity C exponent choice word - 1) + U.card
  calc
    (∑ word ∈ U, lossWordMultiplicity C exponent choice word) =
        ∑ word ∈ U,
          ((lossWordMultiplicity C exponent choice word - 1) + 1) := by
      apply Finset.sum_congr rfl
      intro word hw
      exact hpoint word hw
    _ = (∑ word ∈ U,
          lossWordMultiplicity C exponent choice word - 1) +
          U.card := by simp [Finset.sum_add_distrib]

/-- Original exact cross-coordinate duplicate debt as a sum of
TRUE per-word multiplicity excesses. Every word occurring in m
different slices is charged exactly m-1 times. -/
theorem translatedLossDuplicateDebt_eq_sum_wordMultiplicity_excess
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (choice : V → Fin n) :
    translatedLossDuplicateDebt C exponent choice =
      ∑ word ∈ translatedLossAllCoordinateWords C exponent choice,
        lossWordMultiplicity C exponent choice word - 1 := by
  classical
  have hdouble :=
    lossCoordinateSlice_card_sum_eq_wordMultiplicity_sum
      C exponent choice
  have hexact :=
    lossWordMultiplicity_sum_eq_duplicate_plus_union
      C exponent choice
  unfold translatedLossDuplicateDebt
  rw [hdouble]
  omega

#print axioms lossWordMultiplicity_pos_iff_mem_union
#print axioms lossCoordinateSlice_card_sum_eq_wordMultiplicity_sum
#print axioms lossWordMultiplicity_sum_eq_duplicate_plus_union
#print axioms translatedLossDuplicateDebt_eq_sum_wordMultiplicity_excess

end OrderedEdgeColoring
end JSP000404Research
