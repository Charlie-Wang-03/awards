import JSP000404Research.ResidualTranslatedOverlapFullBranch
import JSP000404Research.ResidualTranslatedOverlapCaptureDichotomy
import JSP000404Research.ResidualCompletionMultiplicity
import Mathlib.Tactic

/-!
# Rigidity of two full blockers

For a nonempty translated overlap cube, a full blocker captures every translated
source word. Two distinct full blockers therefore both contain the translated
image of any fixed source base word, so they form a residual overlap pair.

Moreover a full blocker must inherit every common-inactive source coordinate.
Hence two distinct full blockers inherit the whole common-inactive palette
simultaneously, and the new blocker pair has at least the source free set.

Finally the fixed Boolean translation injects the complete source overlap cube
into the intersection of the two full-blocker completion cubes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_fullBlocker_fullFree
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hfull : w ∈ oneFlipFullBlockers C u v c) :
    commonInactiveRetained C u v ⊆ retainedInactive C w := by
  have hcard :=
    (mem_oneFlipFullBlockers C u v c w).1 hfull
  have hpos :
      0 < (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card :=
    Finset.card_pos.mpr ⟨base,hbase⟩
  rcases oneFlip_blocker_fullFree_or_halfCapture C hc
    with hfree | hhalf
  · exact hfree
  · rw [hcard] at hhalf
    omega

theorem twoFlip_fullBlocker_fullFree
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hfull : w ∈ twoFlipFullBlockers C u v c d) :
    commonInactiveRetained C u v ⊆ retainedInactive C w := by
  have hcard :=
    (mem_twoFlipFullBlockers C u v c d w).1 hfull
  have hpos :
      0 < (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card :=
    Finset.card_pos.mpr ⟨base,hbase⟩
  rcases twoFlip_blocker_fullFree_or_halfCapture C hc hd
    with hfree | hhalf
  · exact hfree
  · rw [hcard] at hhalf
    omega

theorem oneFlip_two_fullBlockers_form_residual_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z) :
    (w < z ∧ IsResidual C w z)
    ∨
    (z < w ∧ IsResidual C z w) := by
  have hyW :=
    oneFlip_fullBlocker_contains_base C hbase hw
  have hyZ :=
    oneFlip_fullBlocker_contains_base C hbase hz
  exact retainedCompletion_overlap_forces_residual
    C hwz hyW hyZ

theorem twoFlip_two_fullBlockers_form_residual_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c d : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hw : w ∈ twoFlipFullBlockers C u v c d)
    (hz : z ∈ twoFlipFullBlockers C u v c d)
    (hwz : w ≠ z) :
    (w < z ∧ IsResidual C w z)
    ∨
    (z < w ∧ IsResidual C z w) := by
  have hyW :=
    twoFlip_fullBlocker_contains_base C hbase hw
  have hyZ :=
    twoFlip_fullBlocker_contains_base C hbase hz
  exact retainedCompletion_overlap_forces_residual
    C hwz hyW hyZ

theorem oneFlip_two_fullBlockers_inherit_commonInactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c) :
    commonInactiveRetained C u v ⊆
      commonInactiveRetained C w z := by
  have hwFree :=
    oneFlip_fullBlocker_fullFree C hbase hc hw
  have hzFree :=
    oneFlip_fullBlocker_fullFree C hbase hc hz
  intro e he
  apply (mem_commonInactiveRetained C w z e).2
  exact ⟨
    (mem_retainedInactive C w e).1 (hwFree he),
    (mem_retainedInactive C z e).1 (hzFree he)⟩

theorem twoFlip_two_fullBlockers_inherit_commonInactive
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
    (hz : z ∈ twoFlipFullBlockers C u v c d) :
    commonInactiveRetained C u v ⊆
      commonInactiveRetained C w z := by
  have hwFree :=
    twoFlip_fullBlocker_fullFree C hbase hc hd hw
  have hzFree :=
    twoFlip_fullBlocker_fullFree C hbase hc hd hz
  intro e he
  apply (mem_commonInactiveRetained C w z e).2
  exact ⟨
    (mem_retainedInactive C w e).1 (hwFree he),
    (mem_retainedInactive C z e).1 (hzFree he)⟩

theorem oneFlip_source_overlap_card_le_two_fullBlocker_intersection
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card
      ≤
    (retainedCompletionWords C w ∩
      retainedCompletionWords C z).card := by
  classical
  let f :
      {x : Fin n → Bool //
        x ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {y : Fin n → Bool //
        y ∈ retainedCompletionWords C w ∩
          retainedCompletionWords C z} :=
    fun x => ⟨flipBoolWordAt x.1 c, by
      apply Finset.mem_inter.mpr
      constructor
      · have hfull :=
          (mem_oneFlipFullBlockers C u v c w).1 hw
        have hsub :
            oneFlipCapturedSourceWords C u v w c ⊆
              retainedCompletionWords C u ∩
                retainedCompletionWords C v := by
          intro q hq
          exact ((mem_oneFlipCapturedSourceWords
            C u v w c q).1 hq).1
        have heq :
            oneFlipCapturedSourceWords C u v w c =
              retainedCompletionWords C u ∩
                retainedCompletionWords C v := by
          apply Finset.eq_of_subset_of_card_le hsub
          rw [hfull]
        have hxCap :
            x.1 ∈ oneFlipCapturedSourceWords C u v w c := by
          rw [heq]
          exact x.2
        exact ((mem_oneFlipCapturedSourceWords
          C u v w c x.1).1 hxCap).2
      · have hfull :=
          (mem_oneFlipFullBlockers C u v c z).1 hz
        have hsub :
            oneFlipCapturedSourceWords C u v z c ⊆
              retainedCompletionWords C u ∩
                retainedCompletionWords C v := by
          intro q hq
          exact ((mem_oneFlipCapturedSourceWords
            C u v z c q).1 hq).1
        have heq :
            oneFlipCapturedSourceWords C u v z c =
              retainedCompletionWords C u ∩
                retainedCompletionWords C v := by
          apply Finset.eq_of_subset_of_card_le hsub
          rw [hfull]
        have hxCap :
            x.1 ∈ oneFlipCapturedSourceWords C u v z c := by
          rw [heq]
          exact x.2
        exact ((mem_oneFlipCapturedSourceWords
          C u v z c x.1).1 hxCap).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply flipBoolWordAt_injective c
    exact congrArg Subtype.val hxy
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective f hf


theorem twoFlip_source_overlap_card_le_two_fullBlocker_intersection
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c d : Fin n}
    (hw : w ∈ twoFlipFullBlockers C u v c d)
    (hz : z ∈ twoFlipFullBlockers C u v c d) :
    (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card
      ≤
    (retainedCompletionWords C w ∩
      retainedCompletionWords C z).card := by
  classical
  let f :
      {x : Fin n → Bool //
        x ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} →
      {y : Fin n → Bool //
        y ∈ retainedCompletionWords C w ∩
          retainedCompletionWords C z} :=
    fun x => ⟨flipBoolWordAt (flipBoolWordAt x.1 c) d, by
      apply Finset.mem_inter.mpr
      constructor
      · have hfull :=
          (mem_twoFlipFullBlockers C u v c d w).1 hw
        have hsub :
            twoFlipCapturedSourceWords C u v w c d ⊆
              retainedCompletionWords C u ∩
                retainedCompletionWords C v := by
          intro q hq
          exact ((mem_twoFlipCapturedSourceWords
            C u v w c d q).1 hq).1
        have heq :
            twoFlipCapturedSourceWords C u v w c d =
              retainedCompletionWords C u ∩
                retainedCompletionWords C v := by
          apply Finset.eq_of_subset_of_card_le hsub
          rw [hfull]
        have hxCap :
            x.1 ∈ twoFlipCapturedSourceWords C u v w c d := by
          rw [heq]
          exact x.2
        exact ((mem_twoFlipCapturedSourceWords
          C u v w c d x.1).1 hxCap).2
      · have hfull :=
          (mem_twoFlipFullBlockers C u v c d z).1 hz
        have hsub :
            twoFlipCapturedSourceWords C u v z c d ⊆
              retainedCompletionWords C u ∩
                retainedCompletionWords C v := by
          intro q hq
          exact ((mem_twoFlipCapturedSourceWords
            C u v z c d q).1 hq).1
        have heq :
            twoFlipCapturedSourceWords C u v z c d =
              retainedCompletionWords C u ∩
                retainedCompletionWords C v := by
          apply Finset.eq_of_subset_of_card_le hsub
          rw [hfull]
        have hxCap :
            x.1 ∈ twoFlipCapturedSourceWords C u v z c d := by
          rw [heq]
          exact x.2
        exact ((mem_twoFlipCapturedSourceWords
          C u v z c d x.1).1 hxCap).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply two_flip_injective c d
    exact congrArg Subtype.val hxy
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

#print axioms oneFlip_fullBlocker_fullFree
#print axioms twoFlip_fullBlocker_fullFree
#print axioms oneFlip_two_fullBlockers_form_residual_pair
#print axioms twoFlip_two_fullBlockers_form_residual_pair
#print axioms oneFlip_two_fullBlockers_inherit_commonInactive
#print axioms twoFlip_two_fullBlockers_inherit_commonInactive
#print axioms oneFlip_source_overlap_card_le_two_fullBlocker_intersection
#print axioms twoFlip_source_overlap_card_le_two_fullBlocker_intersection

end OrderedEdgeColoring
end JSP000404Research
