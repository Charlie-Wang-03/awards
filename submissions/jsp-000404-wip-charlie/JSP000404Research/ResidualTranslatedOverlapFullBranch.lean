import JSP000404Research.ResidualTranslatedOverlapIncidence
import Mathlib.Tactic

/-!
# At most two full-capture blockers

For a nonempty translated overlap cube, a full-capture blocker contains the
translated image of any fixed source base word.  Since one Boolean word has at
most two completion carriers, there can be at most two full blockers.

This gives the finite full-branch bound complementary to the half-capture
decay.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def oneFlipFullBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) : Finset V := by
  classical
  exact Finset.univ.filter fun w =>
    (oneFlipCapturedSourceWords C u v w c).card =
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card

noncomputable def twoFlipFullBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c d : Fin n) : Finset V := by
  classical
  exact Finset.univ.filter fun w =>
    (twoFlipCapturedSourceWords C u v w c d).card =
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card

@[simp] theorem mem_oneFlipFullBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c : Fin n) (w : V) :
    w ∈ oneFlipFullBlockers C u v c ↔
      (oneFlipCapturedSourceWords C u v w c).card =
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card := by
  classical
  simp [oneFlipFullBlockers]

@[simp] theorem mem_twoFlipFullBlockers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (u v : V) (c d : Fin n) (w : V) :
    w ∈ twoFlipFullBlockers C u v c d ↔
      (twoFlipCapturedSourceWords C u v w c d).card =
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card := by
  classical
  simp [twoFlipFullBlockers]

theorem oneFlip_fullBlocker_contains_base
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hfull :
      w ∈ oneFlipFullBlockers C u v c) :
    flipBoolWordAt base c ∈ retainedCompletionWords C w := by
  classical
  have hcard :=
    (mem_oneFlipFullBlockers C u v c w).1 hfull
  have hsub :
      oneFlipCapturedSourceWords C u v w c ⊆
        retainedCompletionWords C u ∩
          retainedCompletionWords C v := by
    intro word hw
    exact
      ((mem_oneFlipCapturedSourceWords
        C u v w c word).1 hw).1
  have heq :
      oneFlipCapturedSourceWords C u v w c =
        retainedCompletionWords C u ∩
          retainedCompletionWords C v := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
  have hbaseCap :
      base ∈ oneFlipCapturedSourceWords C u v w c := by
    rw [heq]
    exact hbase
  exact
    ((mem_oneFlipCapturedSourceWords
      C u v w c base).1 hbaseCap).2

theorem twoFlip_fullBlocker_contains_base
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c d : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hfull :
      w ∈ twoFlipFullBlockers C u v c d) :
    flipBoolWordAt (flipBoolWordAt base c) d ∈
      retainedCompletionWords C w := by
  classical
  have hcard :=
    (mem_twoFlipFullBlockers C u v c d w).1 hfull
  have hsub :
      twoFlipCapturedSourceWords C u v w c d ⊆
        retainedCompletionWords C u ∩
          retainedCompletionWords C v := by
    intro word hw
    exact
      ((mem_twoFlipCapturedSourceWords
        C u v w c d word).1 hw).1
  have heq :
      twoFlipCapturedSourceWords C u v w c d =
        retainedCompletionWords C u ∩
          retainedCompletionWords C v := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
  have hbaseCap :
      base ∈ twoFlipCapturedSourceWords C u v w c d := by
    rw [heq]
    exact hbase
  exact
    ((mem_twoFlipCapturedSourceWords
      C u v w c d base).1 hbaseCap).2

theorem oneFlip_fullBlockers_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v) :
    (oneFlipFullBlockers C u v c).card ≤ 2 := by
  classical
  let f :
      {w : V // w ∈ oneFlipFullBlockers C u v c} → Bool :=
    fun w => bit C w.1 (residualCoord n)
  have hf : Function.Injective f := by
    intro w z hwz
    apply Subtype.ext
    apply completion_carriers_eq_of_residualBit_eq C
    · exact oneFlip_fullBlocker_contains_base
        C hbase w.2
    · exact oneFlip_fullBlocker_contains_base
        C hbase z.2
    · exact hwz
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_bool] using hcard

theorem twoFlip_fullBlockers_card_le_two
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c d : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v) :
    (twoFlipFullBlockers C u v c d).card ≤ 2 := by
  classical
  let f :
      {w : V // w ∈ twoFlipFullBlockers C u v c d} → Bool :=
    fun w => bit C w.1 (residualCoord n)
  have hf : Function.Injective f := by
    intro w z hwz
    apply Subtype.ext
    apply completion_carriers_eq_of_residualBit_eq C
    · exact twoFlip_fullBlocker_contains_base
        C hbase w.2
    · exact twoFlip_fullBlocker_contains_base
        C hbase z.2
    · exact hwz
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_bool] using hcard

#print axioms oneFlip_fullBlockers_card_le_two
#print axioms twoFlip_fullBlockers_card_le_two

end OrderedEdgeColoring
end JSP000404Research
