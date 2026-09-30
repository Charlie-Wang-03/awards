import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Weighted dyadic Hall outlet

For a finite vertex set V with target exponent k(v), encode every unit of
dyadic target mass as

  Sigma v, Fin (2 ^ k(v)).

The cardinality of this sigma type is exactly

  sum_v 2 ^ k(v).

Give each target unit a finite set of admissible n-bit Boolean words.  If these
candidate sets satisfy Hall's condition, Mathlib's Hall marriage theorem gives
an injective representative assignment into the Boolean cube.  Cardinality
then immediately yields

  sum_v 2 ^ k(v) <= 2 ^ n.

Unlike a fixed hard-word-to-old-hole augmenting scheme, this formulation
allows a global rematching of all target units.  Therefore alternating cycles
are harmless: they are absorbed by the matching itself rather than requiring
a terminating path to a pre-existing hole.
-/

namespace JSP000404Research

abbrev DyadicTargetUnit
    {V : Type*}
    (exponent : V → ℕ) :=
  Sigma (fun v : V => Fin (2 ^ exponent v))

theorem card_dyadicTargetUnit
    {V : Type*} [Fintype V]
    (exponent : V → ℕ) :
    Fintype.card (DyadicTargetUnit exponent) =
      ∑ v : V, 2 ^ exponent v := by
  simp [DyadicTargetUnit, Fintype.card_sigma]

theorem dyadic_capacity_of_hall_candidates
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (candidates :
      DyadicTargetUnit exponent →
        Finset (Fin n → Bool))
    (hHall :
      ∀ s : Finset (DyadicTargetUnit exponent),
        s.card ≤ (s.biUnion candidates).card) :
    (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  classical
  obtain ⟨f,hfInj,_hfMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      candidates).1 hHall
  have hcard :
      Fintype.card (DyadicTargetUnit exponent) ≤
        Fintype.card (Fin n → Bool) :=
    Fintype.card_le_of_injective f hfInj
  rw [card_dyadicTargetUnit exponent] at hcard
  simpa [Fintype.card_fun] using hcard

theorem dyadic_capacity_of_hall_candidates_with_membership
    {V : Type*} [Fintype V]
    {n : ℕ}
    (exponent : V → ℕ)
    (candidates :
      DyadicTargetUnit exponent →
        Finset (Fin n → Bool))
    (hHall :
      ∀ s : Finset (DyadicTargetUnit exponent),
        s.card ≤ (s.biUnion candidates).card) :
    ∃ f : DyadicTargetUnit exponent → (Fin n → Bool),
      Function.Injective f ∧
      (∀ x, f x ∈ candidates x) ∧
      (∑ v : V, 2 ^ exponent v) ≤ 2 ^ n := by
  classical
  obtain ⟨f,hfInj,hfMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      candidates).1 hHall
  refine ⟨f,hfInj,hfMem,?_⟩
  have hcard :
      Fintype.card (DyadicTargetUnit exponent) ≤
        Fintype.card (Fin n → Bool) :=
    Fintype.card_le_of_injective f hfInj
  rw [card_dyadicTargetUnit exponent] at hcard
  simpa [Fintype.card_fun] using hcard

#print axioms card_dyadicTargetUnit
#print axioms dyadic_capacity_of_hall_candidates
#print axioms dyadic_capacity_of_hall_candidates_with_membership

end JSP000404Research
