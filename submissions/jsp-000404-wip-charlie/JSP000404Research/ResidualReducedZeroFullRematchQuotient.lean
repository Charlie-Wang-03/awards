import JSP000404Research.ResidualTranslatedOverlapFullPair
import JSP000404Research.ResidualOverlapCube
import Mathlib.Tactic

/-!
# Quotienting equality-dimension reduced-zero full rematches

For a one-flip translation of a nonempty source overlap cube, a full blocker
contains the flipped image of every source word.  Hence two full blockers
contain the entire translated source intersection.

If the new blocker pair has the same common-inactive dimension as the source
pair, the two finite cubes have the same cardinality.  Therefore containment
upgrades to equality: the new intersection is exactly the one-bit translated
source intersection.

Combined with common-inactive inheritance, every two-full-blocker rematch has
the sharp dichotomy

* the common-inactive dimension strictly increases; or
* the rematch is stationary modulo one-bit translation.

This is the reduced-zero analogue of the translated-cube quotient used by the
whole-cube T/T recursion.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_fullBlocker_pair_intersection_eq_image_of_commonInactive_card_eq
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hdim :
      (commonInactiveRetained C w z).card =
        (commonInactiveRetained C u v).card) :
    (retainedCompletionWords C u ∩
        retainedCompletionWords C v).image
          (fun word => flipBoolWordAt word c)
      =
    retainedCompletionWords C w ∩
      retainedCompletionWords C z := by
  classical
  let S :=
    retainedCompletionWords C u ∩
      retainedCompletionWords C v
  let T :=
    retainedCompletionWords C w ∩
      retainedCompletionWords C z
  let f : (Fin n → Bool) → (Fin n → Bool) :=
    fun word => flipBoolWordAt word c

  have hsub : S.image f ⊆ T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_inter.mpr
      ⟨oneFlip_fullBlocker_contains_base C hx hw,
       oneFlip_fullBlocker_contains_base C hx hz⟩

  have hbaseParts := Finset.mem_inter.mp hbase
  have hflipW :
      flipBoolWordAt base c ∈ retainedCompletionWords C w :=
    oneFlip_fullBlocker_contains_base C hbase hw
  have hflipZ :
      flipBoolWordAt base c ∈ retainedCompletionWords C z :=
    oneFlip_fullBlocker_contains_base C hbase hz

  have hcardImage :
      (S.image f).card = S.card := by
    exact Finset.card_image_of_injective
      S (flipBoolWordAt_injective c)

  have hcardS :
      S.card =
        2 ^ (commonInactiveRetained C u v).card := by
    dsimp [S]
    exact retainedCompletionWords_inter_card
      C hbaseParts.1 hbaseParts.2

  have hcardT :
      T.card =
        2 ^ (commonInactiveRetained C w z).card := by
    dsimp [T]
    exact retainedCompletionWords_inter_card
      C hflipW hflipZ

  have hcardEq : (S.image f).card = T.card := by
    rw [hcardImage, hcardS, hcardT, hdim]

  apply Finset.eq_of_subset_of_card_le hsub
  exact le_of_eq hcardEq.symm

/-- Two distinct full blockers either strictly enlarge the free overlap
dimension, or the new overlap is exactly the translated old overlap. -/
theorem oneFlip_two_fullBlockers_dimension_strict_or_translated_quotient
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
    (commonInactiveRetained C u v).card <
        (commonInactiveRetained C w z).card
    ∨
    (retainedCompletionWords C u ∩
        retainedCompletionWords C v).image
          (fun word => flipBoolWordAt word c)
      =
    retainedCompletionWords C w ∩
      retainedCompletionWords C z := by
  have hsub :=
    oneFlip_two_fullBlockers_inherit_commonInactive
      C hbase hcu hw hz
  have hle :
      (commonInactiveRetained C u v).card ≤
        (commonInactiveRetained C w z).card :=
    Finset.card_le_card hsub
  by_cases hlt :
      (commonInactiveRetained C u v).card <
        (commonInactiveRetained C w z).card
  · exact Or.inl hlt
  · right
    have hdim :
        (commonInactiveRetained C w z).card =
          (commonInactiveRetained C u v).card := by
      omega
    exact
      oneFlip_fullBlocker_pair_intersection_eq_image_of_commonInactive_card_eq
        C hbase hw hz hdim

#print axioms
  oneFlip_fullBlocker_pair_intersection_eq_image_of_commonInactive_card_eq
#print axioms
  oneFlip_two_fullBlockers_dimension_strict_or_translated_quotient

end OrderedEdgeColoring
end JSP000404Research
