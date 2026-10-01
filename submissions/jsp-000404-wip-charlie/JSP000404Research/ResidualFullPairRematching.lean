import JSP000404Research.ResidualTranslatedOverlapFullPair
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Equal-mass full transitions are bijections of overlap cubes

Two distinct full blockers w,z contain the complete translated image of the
source overlap cube Q_u ∩ Q_v.  The fixed one- or two-bit translation is
injective.

If the blocker-pair overlap has the same cardinality as the source overlap,
that injection is automatically bijective.  Hence a lossless equal-dimension
full transition is a genuine rematching equivalence between two hard overlap
blocks, not a terminal obstruction.

This is the algebraic ingredient needed to absorb full-transition cycles in a
global Hall matching rather than forcing path termination.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_fullPair_bijective_of_equal_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hcard :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card =
      (retainedCompletionWords C w ∩
        retainedCompletionWords C z).card) :
    ∃ e :
      {x : Fin n → Bool //
        x ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} ≃
      {y : Fin n → Bool //
        y ∈ retainedCompletionWords C w ∩
          retainedCompletionWords C z},
      ∀ x, (e x).1 = flipBoolWordAt x.1 c := by
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
        have hx :
            x.1 ∈ oneFlipCapturedSourceWords C u v w c := by
          rw [heq]
          exact x.2
        exact ((mem_oneFlipCapturedSourceWords
          C u v w c x.1).1 hx).2
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
        have hx :
            x.1 ∈ oneFlipCapturedSourceWords C u v z c := by
          rw [heq]
          exact x.2
        exact ((mem_oneFlipCapturedSourceWords
          C u v z c x.1).1 hx).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply flipBoolWordAt_injective c
    exact congrArg Subtype.val hxy
  have hcardTypes :
      Fintype.card
          {x : Fin n → Bool //
            x ∈ retainedCompletionWords C u ∩
              retainedCompletionWords C v}
        =
      Fintype.card
          {y : Fin n → Bool //
            y ∈ retainedCompletionWords C w ∩
              retainedCompletionWords C z} := by
    simpa only [Fintype.card_coe] using hcard
  have hbij :
      Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hf,hcardTypes⟩
  let e := Equiv.ofBijective f hbij
  refine ⟨e,?_⟩
  intro x
  rfl

theorem twoFlip_fullPair_bijective_of_equal_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c d : Fin n}
    (hw : w ∈ twoFlipFullBlockers C u v c d)
    (hz : z ∈ twoFlipFullBlockers C u v c d)
    (hcard :
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card =
      (retainedCompletionWords C w ∩
        retainedCompletionWords C z).card) :
    ∃ e :
      {x : Fin n → Bool //
        x ∈ retainedCompletionWords C u ∩
          retainedCompletionWords C v} ≃
      {y : Fin n → Bool //
        y ∈ retainedCompletionWords C w ∩
          retainedCompletionWords C z},
      ∀ x,
        (e x).1 =
          flipBoolWordAt (flipBoolWordAt x.1 c) d := by
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
        have hx :
            x.1 ∈ twoFlipCapturedSourceWords C u v w c d := by
          rw [heq]
          exact x.2
        exact ((mem_twoFlipCapturedSourceWords
          C u v w c d x.1).1 hx).2
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
        have hx :
            x.1 ∈ twoFlipCapturedSourceWords C u v z c d := by
          rw [heq]
          exact x.2
        exact ((mem_twoFlipCapturedSourceWords
          C u v z c d x.1).1 hx).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply two_flip_injective c d
    exact congrArg Subtype.val hxy
  have hcardTypes :
      Fintype.card
          {x : Fin n → Bool //
            x ∈ retainedCompletionWords C u ∩
              retainedCompletionWords C v}
        =
      Fintype.card
          {y : Fin n → Bool //
            y ∈ retainedCompletionWords C w ∩
              retainedCompletionWords C z} := by
    simpa only [Fintype.card_coe] using hcard
  have hbij :
      Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hf,hcardTypes⟩
  let e := Equiv.ofBijective f hbij
  refine ⟨e,?_⟩
  intro x
  rfl

#print axioms oneFlip_fullPair_bijective_of_equal_card
#print axioms twoFlip_fullPair_bijective_of_equal_card

end OrderedEdgeColoring
end JSP000404Research
