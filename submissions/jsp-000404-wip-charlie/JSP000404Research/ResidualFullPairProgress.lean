import JSP000404Research.ResidualFullPairRematching
import JSP000404Research.ResidualTranslatedOverlapFullPair
import Mathlib.Tactic

/-!
# Full-pair transition: reversible equality or strict dimension growth

Let u,v carry a nonempty overlap cube and let two distinct full blockers w,z
capture the complete translated source overlap.

The source common-inactive palette is contained in the new blocker-pair
common-inactive palette, and the new overlap cube has cardinality at least the
source overlap cube.

There are only two possibilities.

* Equal overlap mass. Then the fixed pair-local translation is a bijection
  between the two overlap cubes.
* Strictly larger overlap mass. Since every nonempty overlap cube has size
  exactly 2^(card commonInactive), the common-inactive dimension strictly
  increases.

Therefore every non-reversible full transition strictly increases an integer
measure bounded by n.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_two_fullBlockers_equal_rematch_or_dimension_increases
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z) :
    (
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card =
      (retainedCompletionWords C w ∩
        retainedCompletionWords C z).card
      ∧
      ∃ e :
        {x : Fin n → Bool //
          x ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} ≃
        {y : Fin n → Bool //
          y ∈ retainedCompletionWords C w ∩
            retainedCompletionWords C z},
        ∀ x, (e x).1 = flipBoolWordAt x.1 c
    )
    ∨
    (commonInactiveRetained C u v).card <
      (commonInactiveRetained C w z).card := by
  have hsub :=
    oneFlip_two_fullBlockers_inherit_commonInactive
      C hbase hc hw hz
  have hcardLe :=
    oneFlip_source_overlap_card_le_two_fullBlocker_intersection
      C hw hz
  by_cases hEq :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card =
      (retainedCompletionWords C w ∩
        retainedCompletionWords C z).card
  · left
    refine ⟨hEq,?_⟩
    exact oneFlip_fullPair_bijective_of_equal_card
      C hw hz hEq
  · right
    have hcardLt :
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card <
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z).card := by
      omega
    have hyW :=
      oneFlip_fullBlocker_contains_base C hbase hw
    have hyZ :=
      oneFlip_fullBlocker_contains_base C hbase hz
    have hsource :
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card =
        2 ^ (commonInactiveRetained C u v).card := by
      exact retainedCompletionWords_inter_card_eq_pow_commonInactive
        C hbase.1 hbase.2
    have htarget :
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z).card =
        2 ^ (commonInactiveRetained C w z).card := by
      exact retainedCompletionWords_inter_card_eq_pow_commonInactive
        C hyW hyZ
    have hdimLe :
        (commonInactiveRetained C u v).card ≤
          (commonInactiveRetained C w z).card :=
      Finset.card_le_card hsub
    by_contra hnot
    have hdimEq :
        (commonInactiveRetained C u v).card =
          (commonInactiveRetained C w z).card := by
      omega
    rw [hsource, htarget, hdimEq] at hcardLt
    omega

theorem twoFlip_two_fullBlockers_equal_rematch_or_dimension_increases
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c d : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hw : w ∈ twoFlipFullBlockers C u v c d)
    (hz : z ∈ twoFlipFullBlockers C u v c d)
    (hwz : w ≠ z) :
    (
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card =
      (retainedCompletionWords C w ∩
        retainedCompletionWords C z).card
      ∧
      ∃ e :
        {x : Fin n → Bool //
          x ∈ retainedCompletionWords C u ∩
            retainedCompletionWords C v} ≃
        {y : Fin n → Bool //
          y ∈ retainedCompletionWords C w ∩
            retainedCompletionWords C z},
        ∀ x,
          (e x).1 =
            flipBoolWordAt (flipBoolWordAt x.1 c) d
    )
    ∨
    (commonInactiveRetained C u v).card <
      (commonInactiveRetained C w z).card := by
  have hsub :=
    twoFlip_two_fullBlockers_inherit_commonInactive
      C hbase hc hd hw hz
  have hcardLe :=
    twoFlip_source_overlap_card_le_two_fullBlocker_intersection
      C hw hz
  by_cases hEq :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card =
      (retainedCompletionWords C w ∩
        retainedCompletionWords C z).card
  · left
    refine ⟨hEq,?_⟩
    exact twoFlip_fullPair_bijective_of_equal_card
      C hw hz hEq
  · right
    have hcardLt :
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card <
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z).card := by
      omega
    have hyW :=
      twoFlip_fullBlocker_contains_base C hbase hw
    have hyZ :=
      twoFlip_fullBlocker_contains_base C hbase hz
    have hsource :
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card =
        2 ^ (commonInactiveRetained C u v).card := by
      exact retainedCompletionWords_inter_card_eq_pow_commonInactive
        C hbase.1 hbase.2
    have htarget :
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z).card =
        2 ^ (commonInactiveRetained C w z).card := by
      exact retainedCompletionWords_inter_card_eq_pow_commonInactive
        C hyW hyZ
    have hdimLe :
        (commonInactiveRetained C u v).card ≤
          (commonInactiveRetained C w z).card :=
      Finset.card_le_card hsub
    by_contra hnot
    have hdimEq :
        (commonInactiveRetained C u v).card =
          (commonInactiveRetained C w z).card := by
      omega
    rw [hsource, htarget, hdimEq] at hcardLt
    omega

theorem commonInactive_card_le_n
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) :
    (commonInactiveRetained C u v).card ≤ n := by
  simpa using
    Finset.card_le_univ (commonInactiveRetained C u v)

#print axioms oneFlip_two_fullBlockers_equal_rematch_or_dimension_increases
#print axioms twoFlip_two_fullBlockers_equal_rematch_or_dimension_increases
#print axioms commonInactive_card_le_n

end OrderedEdgeColoring
end JSP000404Research
