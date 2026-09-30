import JSP000404Research.ResidualCompletionAccounting
import JSP000404Research.ResidualTranslatedOverlapHalfCapture
import JSP000404Research.ResidualTranslatedOverlapHalfCaptureTwo
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
# Total blocker-incidence budget for a fixed pair displacement

For a fixed one- or two-bit displacement of one source overlap cube, define
B_w to be the source words whose displaced images lie in Q_w.

Double counting source/blocker incidences gives

  sum_w card(B_w)
    = sum_x blockerLoad(displaced x).

Every displaced Boolean word belongs to at most two retained completion cubes,
so the total blocker incidence is at most twice the source overlap mass.

This is the global incidence budget for one carrier.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem sum_oneFlipCaptured_le_two_mul_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c : Fin n} :
    (∑ w : V, (oneFlipCapturedSourceWords C u v w c).card)
      ≤
    2 * (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card := by
  classical
  let source :=
    retainedCompletionWords C u ∩ retainedCompletionWords C v
  let B : V → Finset (Fin n → Bool) :=
    fun w => oneFlipCapturedSourceWords C u v w c
  have hdc :=
    Finset.sum_card_eq_sum_biUnion_card
      B (Finset.univ : Finset V)
  have hunionSub :
      (Finset.univ : Finset V).biUnion B ⊆ source := by
    intro word hword
    obtain ⟨w,_hwUniv,hwB⟩ := Finset.mem_biUnion.mp hword
    have hdata :=
      (mem_oneFlipCapturedSourceWords
        C u v w c word).1 hwB
    exact hdata.1
  have hload :
      ∀ word ∈ (Finset.univ : Finset V).biUnion B,
        ({w | w ∈ (Finset.univ : Finset V) ∧ word ∈ B w} :
          Finset V).card ≤ 2 := by
    intro word hword
    have hsub :
        ({w | w ∈ (Finset.univ : Finset V) ∧ word ∈ B w} :
          Finset V)
          ⊆ completionFibre C (flipBoolWordAt word c) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hdata :=
        (mem_oneFlipCapturedSourceWords
          C u v w c word).1 hw
      exact (mem_completionFibre
        C (flipBoolWordAt word c) w).2 hdata.2
    exact
      (Finset.card_le_card hsub).trans
        (completionFibre_card_le_two
          C (flipBoolWordAt word c))
  calc
    (∑ w : V, (oneFlipCapturedSourceWords C u v w c).card)
        =
      ∑ w ∈ (Finset.univ : Finset V), (B w).card := by
        simp [B]
    _ =
      ∑ word ∈ (Finset.univ : Finset V).biUnion B,
        ({w | w ∈ (Finset.univ : Finset V) ∧ word ∈ B w} :
          Finset V).card := hdc
    _ ≤
      ∑ _word ∈ (Finset.univ : Finset V).biUnion B, 2 := by
        apply Finset.sum_le_sum
        intro word hword
        exact hload word hword
    _ =
      2 * ((Finset.univ : Finset V).biUnion B).card := by
        simp [Nat.mul_comm]
    _ ≤ 2 * source.card := by
        exact Nat.mul_le_mul_left 2
          (Finset.card_le_card hunionSub)
    _ =
      2 * (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
        rfl

theorem sum_twoFlipCaptured_le_two_mul_overlap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v : V} {c d : Fin n} :
    (∑ w : V, (twoFlipCapturedSourceWords C u v w c d).card)
      ≤
    2 * (retainedCompletionWords C u ∩
      retainedCompletionWords C v).card := by
  classical
  let source :=
    retainedCompletionWords C u ∩ retainedCompletionWords C v
  let B : V → Finset (Fin n → Bool) :=
    fun w => twoFlipCapturedSourceWords C u v w c d
  have hdc :=
    Finset.sum_card_eq_sum_biUnion_card
      B (Finset.univ : Finset V)
  have hunionSub :
      (Finset.univ : Finset V).biUnion B ⊆ source := by
    intro word hword
    obtain ⟨w,_hwUniv,hwB⟩ := Finset.mem_biUnion.mp hword
    have hdata :=
      (mem_twoFlipCapturedSourceWords
        C u v w c d word).1 hwB
    exact hdata.1
  have hload :
      ∀ word ∈ (Finset.univ : Finset V).biUnion B,
        ({w | w ∈ (Finset.univ : Finset V) ∧ word ∈ B w} :
          Finset V).card ≤ 2 := by
    intro word hword
    have hsub :
        ({w | w ∈ (Finset.univ : Finset V) ∧ word ∈ B w} :
          Finset V)
          ⊆ completionFibre C
            (flipBoolWordAt (flipBoolWordAt word c) d) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hdata :=
        (mem_twoFlipCapturedSourceWords
          C u v w c d word).1 hw
      exact (mem_completionFibre
        C (flipBoolWordAt (flipBoolWordAt word c) d) w).2
          hdata.2
    exact
      (Finset.card_le_card hsub).trans
        (completionFibre_card_le_two
          C (flipBoolWordAt (flipBoolWordAt word c) d))
  calc
    (∑ w : V, (twoFlipCapturedSourceWords C u v w c d).card)
        =
      ∑ w ∈ (Finset.univ : Finset V), (B w).card := by
        simp [B]
    _ =
      ∑ word ∈ (Finset.univ : Finset V).biUnion B,
        ({w | w ∈ (Finset.univ : Finset V) ∧ word ∈ B w} :
          Finset V).card := hdc
    _ ≤
      ∑ _word ∈ (Finset.univ : Finset V).biUnion B, 2 := by
        apply Finset.sum_le_sum
        intro word hword
        exact hload word hword
    _ =
      2 * ((Finset.univ : Finset V).biUnion B).card := by
        simp [Nat.mul_comm]
    _ ≤ 2 * source.card := by
        exact Nat.mul_le_mul_left 2
          (Finset.card_le_card hunionSub)
    _ =
      2 * (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card := by
        rfl

#print axioms sum_oneFlipCaptured_le_two_mul_overlap
#print axioms sum_twoFlipCaptured_le_two_mul_overlap

end OrderedEdgeColoring
end JSP000404Research
