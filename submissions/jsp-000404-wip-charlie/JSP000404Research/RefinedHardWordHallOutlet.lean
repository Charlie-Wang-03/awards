import JSP000404Research.HardWordHallOutlet
import JSP000404Research.RefinedResidualHardRemainder
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Tactic

/-!
# Refined Hall outlet using Boolean holes plus unused strict-overlap surplus

The sharp residual accounting leaves a concrete reserve after paying the
strict--strict overlap:

  remainingStrictPaymentSurplus
    = totalProfileSurplus - card(strictStrictOverlapWords).

Therefore the correct lower-branch system of distinct representatives does not
need to send every hard word to a Boolean hole.  It may send a hard word either

* to a genuine uncovered Boolean word, or
* to one unit of the remaining strict-overlap surplus.

Hall's theorem on this enlarged target type is exactly sufficient for the
sharp 2^n capacity.

In a zero-minimum minimal overweight counterexample this target type has
cardinality exactly one less than the hard-word type, so one additional
geometric/deletion target would contradict minimality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

abbrev ProjectionHoleOrRemainingSurplus
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :=
  Sum (ProjectionHoleWord C)
    (Fin (remainingStrictPaymentSurplus C exponent))

/-- Hall on holes plus the unused strict-overlap surplus produces the refined
global hard-word injection needed for the sharp lower branch. -/
theorem exists_refined_hardProjectionWord_injection_of_hall
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (targets :
      HardProjectionWord C exponent →
        Finset (ProjectionHoleOrRemainingSurplus C exponent))
    (hHall :
      ∀ s : Finset (HardProjectionWord C exponent),
        s.card ≤ (s.biUnion targets).card) :
    ∃ f :
        HardProjectionWord C exponent →
          ProjectionHoleOrRemainingSurplus C exponent,
      Function.Injective f ∧
        ∀ x, f x ∈ targets x := by
  exact
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      targets).1 hHall

/-- Refined Hall capacity outlet for the lower branch. -/
theorem exponent_capacity_of_refined_hardProjectionWord_hall
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (targets :
      HardProjectionWord C exponent →
        Finset (ProjectionHoleOrRemainingSurplus C exponent))
    (hHall :
      ∀ s : Finset (HardProjectionWord C exponent),
        s.card ≤ (s.biUnion targets).card) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  obtain ⟨f, hf, _hmem⟩ :=
    exists_refined_hardProjectionWord_injection_of_hall
      C exponent targets hHall
  have hcard :
      (hardProjectionWords C exponent).card ≤
        (projectionHoleWords C).card +
          remainingStrictPaymentSurplus C exponent := by
    have h :=
      Fintype.card_le_of_injective f hf
    simpa [HardProjectionWord,
      ProjectionHoleOrRemainingSurplus,
      ProjectionHoleWord,
      Fintype.card_sum,
      Fintype.card_coe,
      Fintype.card_fin] using h
  exact exponent_capacity_of_refined_hard_words_payment
    C exponent hexp honeLoss hcard

/-- Cardinal obstruction in an exact-one overweight configuration: no
injection into the refined target type can exist.  This is the contradiction
endpoint for any explicit augmenting construction. -/
theorem no_refined_hardProjectionWord_injection_of_target_eq_bound_add_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (htarget :
      (∑ v, 2 ^ exponent v) = 2 ^ n + 1) :
    ¬ ∃ f :
        HardProjectionWord C exponent →
          ProjectionHoleOrRemainingSurplus C exponent,
      Function.Injective f := by
  intro hex
  obtain ⟨f, hf⟩ := hex
  have hcard :
      (hardProjectionWords C exponent).card ≤
        (projectionHoleWords C).card +
          remainingStrictPaymentSurplus C exponent := by
    have h :=
      Fintype.card_le_of_injective f hf
    simpa [HardProjectionWord,
      ProjectionHoleOrRemainingSurplus,
      ProjectionHoleWord,
      Fintype.card_sum,
      Fintype.card_coe,
      Fintype.card_fin] using h
  have heq :=
    hardProjectionWords_card_eq_holes_add_remainingSurplus_add_one
      C exponent hexp honeLoss htarget
  omega

#print axioms exists_refined_hardProjectionWord_injection_of_hall
#print axioms exponent_capacity_of_refined_hardProjectionWord_hall
#print axioms no_refined_hardProjectionWord_injection_of_target_eq_bound_add_one

end OrderedEdgeColoring
end JSP000404Research
