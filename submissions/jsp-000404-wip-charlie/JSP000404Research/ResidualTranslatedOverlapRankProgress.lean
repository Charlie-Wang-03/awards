import JSP000404Research.ResidualWeightedRecursionRank
import JSP000404Research.ResidualTranslatedOverlapCaptureTrichotomy
import JSP000404Research.ResidualFullPairProgress
import Mathlib.Tactic

/-!
# Rank decrease for actual translated-overlap recursion steps

Connect the abstract rank from ResidualWeightedRecursionRank to the concrete
translated-overlap transition theorems.

Small branch.
If a blocker captures a positive, non-full part of a translated overlap cube,
the exact capture trichotomy forces capture <= half of the source mass.
Therefore the carried payload strictly decreases, and the weighted recursion
rank decreases regardless of the next free dimension.

Full branch.
If two distinct full blockers form the lossless continuation, then
ResidualFullPairProgress gives either an explicit equal-card rematching
equivalence or a strict increase in common-inactive dimension.  In the latter
case the same payload has strictly smaller weighted recursion rank.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_positive_nonfull_capture_payload_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    (hc : c ∈ retainedActive C u)
    (hpos :
      0 < (oneFlipCapturedSourceWords C u v w c).card)
    (hnotFull :
      (oneFlipCapturedSourceWords C u v w c).card ≠
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card) :
    (oneFlipCapturedSourceWords C u v w c).card <
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  rcases oneFlip_capture_zero_full_or_half C hc
    with hzero | hfull | hhalf
  · omega
  · exact False.elim (hnotFull hfull)
  · apply payload_strictly_decreases_of_half_capture
      (payload :=
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card)
      (captured :=
        (oneFlipCapturedSourceWords C u v w c).card)
    · omega
    · exact hhalf
    · exact hpos

theorem twoFlip_positive_nonfull_capture_payload_lt
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hpos :
      0 < (twoFlipCapturedSourceWords C u v w c d).card)
    (hnotFull :
      (twoFlipCapturedSourceWords C u v w c d).card ≠
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card) :
    (twoFlipCapturedSourceWords C u v w c d).card <
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
  rcases twoFlip_capture_zero_full_or_half C hc hd
    with hzero | hfull | hhalf
  · omega
  · exact False.elim (hnotFull hfull)
  · apply payload_strictly_decreases_of_half_capture
      (payload :=
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card)
      (captured :=
        (twoFlipCapturedSourceWords C u v w c d).card)
    · omega
    · exact hhalf
    · exact hpos

theorem oneFlip_positive_nonfull_capture_rank_decreases
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    {nextFreeDim : ℕ}
    (hc : c ∈ retainedActive C u)
    (hnext : nextFreeDim ≤ n)
    (hpos :
      0 < (oneFlipCapturedSourceWords C u v w c).card)
    (hnotFull :
      (oneFlipCapturedSourceWords C u v w c).card ≠
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card) :
    weightedHardStateRank n
        (oneFlipCapturedSourceWords C u v w c).card
        nextFreeDim
      <
    weightedHardStateRank n
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        (commonInactiveRetained C u v).card := by
  apply weightedHardStateRank_lt_of_payload_lt
  · exact commonInactive_card_le_n C u v
  · exact hnext
  · exact oneFlip_positive_nonfull_capture_payload_lt
      C hc hpos hnotFull

theorem twoFlip_positive_nonfull_capture_rank_decreases
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    {nextFreeDim : ℕ}
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hnext : nextFreeDim ≤ n)
    (hpos :
      0 < (twoFlipCapturedSourceWords C u v w c d).card)
    (hnotFull :
      (twoFlipCapturedSourceWords C u v w c d).card ≠
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card) :
    weightedHardStateRank n
        (twoFlipCapturedSourceWords C u v w c d).card
        nextFreeDim
      <
    weightedHardStateRank n
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        (commonInactiveRetained C u v).card := by
  apply weightedHardStateRank_lt_of_payload_lt
  · exact commonInactive_card_le_n C u v
  · exact hnext
  · exact twoFlip_positive_nonfull_capture_payload_lt
      C hc hd hpos hnotFull

theorem oneFlip_fullPair_rematch_or_rank_decreases
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
    weightedHardStateRank n
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        (commonInactiveRetained C w z).card
      <
    weightedHardStateRank n
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        (commonInactiveRetained C u v).card := by
  rcases
    oneFlip_two_fullBlockers_equal_rematch_or_dimension_increases
      C hbase hc hw hz hwz
    with hrematch | hdim
  · exact Or.inl hrematch.2
  · right
    exact weightedHardStateRank_lt_of_dimension_growth
      (commonInactive_card_le_n C u v)
      (commonInactive_card_le_n C w z)
      hdim

theorem twoFlip_fullPair_rematch_or_rank_decreases
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
    weightedHardStateRank n
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        (commonInactiveRetained C w z).card
      <
    weightedHardStateRank n
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card
        (commonInactiveRetained C u v).card := by
  rcases
    twoFlip_two_fullBlockers_equal_rematch_or_dimension_increases
      C hbase hc hd hw hz hwz
    with hrematch | hdim
  · exact Or.inl hrematch.2
  · right
    exact weightedHardStateRank_lt_of_dimension_growth
      (commonInactive_card_le_n C u v)
      (commonInactive_card_le_n C w z)
      hdim

#print axioms oneFlip_positive_nonfull_capture_rank_decreases
#print axioms twoFlip_positive_nonfull_capture_rank_decreases
#print axioms oneFlip_fullPair_rematch_or_rank_decreases
#print axioms twoFlip_fullPair_rematch_or_rank_decreases

end OrderedEdgeColoring
end JSP000404Research
