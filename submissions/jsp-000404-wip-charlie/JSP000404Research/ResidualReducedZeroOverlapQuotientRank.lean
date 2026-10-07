import JSP000404Research.ResidualReducedZeroOverlapTranslationQuotient
import Mathlib.Tactic

/-!
# Cardinality rank on the reduced-zero overlap translation quotient

Coordinate flips are bijections of Boolean words. Consequently every one-flip
overlap step preserves finite-set cardinality, and so does its equivalence
closure. Cardinality therefore descends to the overlap translation quotient.

For a distinct two-full-blocker rematch, the sharp reduced-zero dichotomy can
then be expressed as:

* the quotient cardinality rank strictly increases; or
* the quotient state is unchanged.

This is the monotone quotient-level form needed for a later finite recursion
argument.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlipOverlapRel_card_eq
    {n : ℕ}
    {S T : Finset (Fin n → Bool)}
    (h : oneFlipOverlapRel S T) :
    S.card = T.card := by
  rcases h with ⟨c,rfl⟩
  exact
    (Finset.card_image_of_injective
      S (flipBoolWordAt_injective c)).symm

theorem overlapTranslationEquivalent_card_eq
    {n : ℕ}
    {S T : Finset (Fin n → Bool)}
    (h : OverlapTranslationEquivalent S T) :
    S.card = T.card := by
  induction h with
  | rel _ _ hrel =>
      exact oneFlipOverlapRel_card_eq hrel
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

noncomputable def overlapTranslationCard
    {n : ℕ} :
    OverlapTranslationQuotient n → ℕ :=
  Quotient.lift Finset.card (by
    intro S T h
    exact overlapTranslationEquivalent_card_eq h)

@[simp] theorem overlapTranslationCard_mk
    {n : ℕ}
    (S : Finset (Fin n → Bool)) :
    overlapTranslationCard
        (Quotient.mk (overlapTranslationSetoid n) S)
      = S.card := by
  rfl

theorem oneFlip_two_fullBlockers_overlap_rank_strict_or_same_quotient
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z) :
    overlapTranslationCard
        (Quotient.mk
          (overlapTranslationSetoid n)
          (retainedCompletionWords C u ∩
            retainedCompletionWords C v))
      <
    overlapTranslationCard
        (Quotient.mk
          (overlapTranslationSetoid n)
          (retainedCompletionWords C w ∩
            retainedCompletionWords C z))
    ∨
    Quotient.mk
        (overlapTranslationSetoid n)
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v)
      =
    Quotient.mk
        (overlapTranslationSetoid n)
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z) := by
  rcases
      oneFlip_two_fullBlockers_dimension_strict_or_same_overlap_quotient
        C hbase hcu hw hz hwz
    with hdim | hsame
  · left
    have hbaseParts := Finset.mem_inter.mp hbase
    have hflipW :
        flipBoolWordAt base c ∈ retainedCompletionWords C w :=
      oneFlip_fullBlocker_contains_base C hbase hw
    have hflipZ :
        flipBoolWordAt base c ∈ retainedCompletionWords C z :=
      oneFlip_fullBlocker_contains_base C hbase hz
    have hcardS :
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
          =
        2 ^ (commonInactiveRetained C u v).card :=
      retainedCompletionWords_inter_card_eq_pow_commonInactive
        C hbaseParts.1 hbaseParts.2
    have hcardT :
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z).card
          =
        2 ^ (commonInactiveRetained C w z).card :=
      retainedCompletionWords_inter_card_eq_pow_commonInactive
        C hflipW hflipZ
    rw [overlapTranslationCard_mk,
      overlapTranslationCard_mk,
      hcardS,hcardT]
    exact Nat.pow_lt_pow_right
      (by norm_num : 1 < 2) hdim
  · exact Or.inr hsame

#print axioms oneFlipOverlapRel_card_eq
#print axioms overlapTranslationEquivalent_card_eq
#print axioms overlapTranslationCard
#print axioms
  oneFlip_two_fullBlockers_overlap_rank_strict_or_same_quotient

end OrderedEdgeColoring
end JSP000404Research
