import JSP000404Research.ResidualTranslatedOverlapFullBranch
import JSP000404Research.ResidualTranslatedOverlapCaptureDichotomy
import Mathlib.Tactic

/-!
# Two full blockers form a dimension-preserving residual successor

Assume a nonempty source overlap cube and a fixed one-bit translation.

If two distinct vertices w,z are full-capture blockers, then:

* both inherit every common-inactive source coordinate;
* every translated source word belongs to both Q_w and Q_z;
* w,z form a residual pair (in one order or the other);
* no third completion carrier can contain any translated source word.

Thus the only non-decaying branch of the collision tree is a genuine
dimension-preserving transition to a new residual carrier pair.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_fullBlocker_inherits_all_commonInactive
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hfull :
      w ∈ oneFlipFullBlockers C u v c) :
    commonInactiveRetained C u v ⊆ retainedInactive C w := by
  have hsourcePos :
      0 < (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card :=
    Finset.card_pos.mpr ⟨base,hbase⟩
  have hfullCard :=
    (mem_oneFlipFullBlockers C u v c w).1 hfull
  rcases oneFlip_blocker_fullFree_or_halfCapture C hc
    with hfree | hhalf
  · exact hfree
  · rw [hfullCard] at hhalf
    omega

theorem oneFlip_fullBlocker_contains_all
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hfull :
      w ∈ oneFlipFullBlockers C u v c) :
    ∀ word,
      word ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v →
      flipBoolWordAt word c ∈ retainedCompletionWords C w := by
  have hfree :=
    oneFlip_fullBlocker_inherits_all_commonInactive
      C hbase hc hfull
  have hbaseW :=
    oneFlip_fullBlocker_contains_base
      C hbase hfull
  exact oneFlip_fullFree_nonempty_capture_is_full
    C hfree hbase hbaseW

theorem oneFlip_two_fullBlockers_residual_successor
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hwFull :
      w ∈ oneFlipFullBlockers C u v c)
    (hzFull :
      z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z) :
    commonInactiveRetained C u v ⊆ retainedInactive C w ∧
    commonInactiveRetained C u v ⊆ retainedInactive C z ∧
    (IsResidual C w z ∨ IsResidual C z w) ∧
    ∀ word,
      word ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v →
      completionFibre C (flipBoolWordAt word c) = {w,z} := by
  have hwFree :=
    oneFlip_fullBlocker_inherits_all_commonInactive
      C hbase hc hwFull
  have hzFree :=
    oneFlip_fullBlocker_inherits_all_commonInactive
      C hbase hc hzFull
  have hwBase :=
    oneFlip_fullBlocker_contains_base C hbase hwFull
  have hzBase :=
    oneFlip_fullBlocker_contains_base C hbase hzFull
  have hres :=
    retainedCompletion_overlap_forces_residual
      C hwz hwBase hzBase
  refine ⟨hwFree,hzFree,hres,?_⟩
  intro word hword
  have hw :=
    oneFlip_fullBlocker_contains_all
      C hbase hc hwFull word hword
  have hz :=
    oneFlip_fullBlocker_contains_all
      C hbase hc hzFull word hword
  have hwF :
      w ∈ completionFibre C (flipBoolWordAt word c) :=
    (mem_completionFibre C _ w).2 hw
  have hzF :
      z ∈ completionFibre C (flipBoolWordAt word c) :=
    (mem_completionFibre C _ z).2 hz
  have hle :=
    completionFibre_card_le_two
      C (flipBoolWordAt word c)
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    have hcardLower :
        2 ≤ (completionFibre C (flipBoolWordAt word c)).card := by
      have hnontrivial :
          (completionFibre C (flipBoolWordAt word c)).Nontrivial :=
        ⟨w,hwF,z,hzF,hwz⟩
      exact hnontrivial.two_le_card
    have hcardEq :
        (completionFibre C (flipBoolWordAt word c)).card = 2 := by
      omega
    have hpairCard : ({w,z} : Finset V).card = 2 := by
      simp [hwz]
    have hxPair : x = w ∨ x = z := by
      by_contra hxne
      push_neg at hxne
      have hthree :
          ({w,z,x} : Finset V).card = 3 := by
        simp [hwz,hxne.1,hxne.2]
      have hsub :
          ({w,z,x} : Finset V) ⊆
            completionFibre C (flipBoolWordAt word c) := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hwF
        · exact hzF
        · exact hx
      have := Finset.card_le_card hsub
      rw [hthree,hcardEq] at this
      omega
    simpa [hxPair]
  · have hcardLower :
        2 ≤ (completionFibre C (flipBoolWordAt word c)).card := by
      have hnontrivial :
          (completionFibre C (flipBoolWordAt word c)).Nontrivial :=
        ⟨w,hwF,z,hzF,hwz⟩
      exact hnontrivial.two_le_card
    have hcardEq :
        (completionFibre C (flipBoolWordAt word c)).card = 2 := by
      omega
    simp [hwz,hcardEq]

#print axioms oneFlip_fullBlocker_inherits_all_commonInactive
#print axioms oneFlip_two_fullBlockers_residual_successor

end OrderedEdgeColoring
end JSP000404Research
