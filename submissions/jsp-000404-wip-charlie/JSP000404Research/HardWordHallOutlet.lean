import JSP000404Research.PlanarLowerBranchHardWordInjection
import JSP000404Research.PlanarUpperBranchHardDefect
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Tactic

/-!
# Hall outlets for the global hard-word displacement problem

The remaining residual problem is a finite system-of-distinct-representatives
problem.

For the sharp lower branch, each hard projection word is assigned a finite set
of admissible global Boolean holes.  Hall's condition on every finite subfamily
then produces an injective choice of holes, and the existing hard-word outlet
closes the capacity theorem.

For the upper branch, allow an auxiliary finite set of slack tokens.  A Hall
matching into

  global holes ⊕ slack tokens

gives exactly the relaxed hard-defect inequality.  Taking the number of slack
tokens to be 2^(n-2) recovers the upper Sendov capacity constant.

This module is purely finite and arbitrary-cardinality.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

open scoped BigOperators

abbrev HardProjectionWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :=
  {word // word ∈ hardProjectionWords C exponent}

abbrev ProjectionHoleWord
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :=
  {word // word ∈ projectionHoleWords C}

/-- Hall's condition on an arbitrary candidate-hole family produces the exact
injective hard-word-to-hole assignment needed by the lower branch. -/
theorem exists_hardProjectionWord_injection_of_hall
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (targets :
      HardProjectionWord C exponent →
        Finset (ProjectionHoleWord C))
    (hHall :
      ∀ s : Finset (HardProjectionWord C exponent),
        s.card ≤ (s.biUnion targets).card) :
    ∃ f :
        HardProjectionWord C exponent →
          ProjectionHoleWord C,
      Function.Injective f ∧
        ∀ x, f x ∈ targets x := by
  exact
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      targets).1 hHall

/-- Direct lower-branch capacity outlet from a Hall family of genuine global
holes. -/
theorem exponent_capacity_of_hardProjectionWord_hall
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (targets :
      HardProjectionWord C exponent →
        Finset (ProjectionHoleWord C))
    (hHall :
      ∀ s : Finset (HardProjectionWord C exponent),
        s.card ≤ (s.biUnion targets).card) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n := by
  obtain ⟨f, hf, _hmem⟩ :=
    exists_hardProjectionWord_injection_of_hall
      C exponent targets hHall
  exact exponent_capacity_of_hardProjectionWords_injection
    C exponent hexp honeLoss f hf

/-- Upper-branch target type: either a genuine Boolean hole or one of a fixed
finite number of slack tokens. -/
abbrev ProjectionHoleOrSlack
    {V : Type*} [LinearOrder V] [Fintype V] {n slack : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :=
  Sum (ProjectionHoleWord C) (Fin slack)

/-- Hall's condition with slack tokens gives an injective global assignment. -/
theorem exists_hardProjectionWord_injection_with_slack_of_hall
    {V : Type*} [LinearOrder V] [Fintype V] {n slack : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (targets :
      HardProjectionWord C exponent →
        Finset (ProjectionHoleOrSlack (C := C) (slack := slack)))
    (hHall :
      ∀ s : Finset (HardProjectionWord C exponent),
        s.card ≤ (s.biUnion targets).card) :
    ∃ f :
        HardProjectionWord C exponent →
          ProjectionHoleOrSlack (C := C) (slack := slack),
      Function.Injective f ∧
        ∀ x, f x ∈ targets x := by
  exact
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      targets).1 hHall

/-- A Hall matching into holes plus slack tokens implies the corresponding
relaxed dyadic capacity. -/
theorem exponent_capacity_of_hardProjectionWord_hall_with_slack
    {V : Type*} [LinearOrder V] [Fintype V] {n slack : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (targets :
      HardProjectionWord C exponent →
        Finset (ProjectionHoleOrSlack (C := C) (slack := slack)))
    (hHall :
      ∀ s : Finset (HardProjectionWord C exponent),
        s.card ≤ (s.biUnion targets).card) :
    (∑ v, 2 ^ exponent v) ≤ 2 ^ n + slack := by
  obtain ⟨f, hf, _hmem⟩ :=
    exists_hardProjectionWord_injection_with_slack_of_hall
      C exponent targets hHall
  have hcard :
      (hardProjectionWords C exponent).card ≤
        (projectionHoleWords C).card + slack := by
    have h :=
      Fintype.card_le_of_injective f hf
    simpa [HardProjectionWord, ProjectionHoleOrSlack,
      ProjectionHoleWord, Fintype.card_sum,
      Fintype.card_coe, Fintype.card_fin] using h
  rw [hardProjectionWords_card_eq C exponent hexp honeLoss,
      projectionHoleWords_card C] at hcard
  exact exponent_capacity_of_hard_words_fit_holes_with_slack
    C exponent hexp honeLoss hcard

/-- The exact upper Sendov allowance is obtained with 2^(n-2) slack tokens. -/
theorem exponent_capacity_of_quarterSlack_hall
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (targets :
      HardProjectionWord C exponent →
        Finset
          (ProjectionHoleOrSlack
            (C := C) (slack := 2 ^ (n - 2))))
    (hHall :
      ∀ s : Finset (HardProjectionWord C exponent),
        s.card ≤ (s.biUnion targets).card) :
    (∑ v, 2 ^ exponent v) ≤
      2 ^ n + 2 ^ (n - 2) := by
  exact exponent_capacity_of_hardProjectionWord_hall_with_slack
    C exponent hexp honeLoss targets hHall

#print axioms exists_hardProjectionWord_injection_of_hall
#print axioms exponent_capacity_of_hardProjectionWord_hall
#print axioms exists_hardProjectionWord_injection_with_slack_of_hall
#print axioms exponent_capacity_of_hardProjectionWord_hall_with_slack
#print axioms exponent_capacity_of_quarterSlack_hall

end OrderedEdgeColoring
end JSP000404Research
