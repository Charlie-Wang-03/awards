import JSP000404Research.ResidualLossActiveFlipBlocker
import Mathlib.Tactic

/-!
# Opposite-bit witness for every genuinely covered projected-loss translate

The exact global six-source debt identity isolates covered translated-loss
words as an unpaid term. Choosing retained-active loss flips removes
spurious "covered by oneself" cases.

Each remaining translated word has an actual distinct blocker w, and the
common active retained coordinate c has opposite canonical bits at the
projected-loss owner v and the blocker w. No new AngleCap assumption,
no invented true-hole credit and no global injection are used.

This identifies the precise *orientational* configuration to be paid by
future geometric arguments, instead of simply counting an arbitrary cover.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translatedLossCoveredWord_has_opposite_active_bits
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (choice : V → Fin n)
    (hchoice : ∀ v ∈ projectedLossVertices C exponent,
      choice v ∈ retainedActive C v)
    {word : Fin n → Bool}
    (hcovered :
      word ∈ translatedLossCoveredWords C exponent choice) :
    ∃ v ∈ projectedLossVertices C exponent,
      ∃ w : V, v ≠ w ∧
        ∃ c : Fin n,
          c ∈ retainedActive C v ∧
          c ∈ retainedActive C w ∧
          retainedBit C w c = !(retainedBit C v c) ∧
          word ∈ translatedCompletionWords C v c ∧
          word ∈ retainedCompletionWords C w := by
  obtain ⟨v, hv, w, hvw, c, hcv, hcw, hword, hw⟩ :=
    translatedLossCoveredWord_has_distinct_shared_active_blocker
      C exponent hexp honeLoss choice hchoice hcovered
  have hsource :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hword
  have hdest :
      flipBoolWordAt (flipBoolWordAt word c) c ∈
        retainedCompletionWords C w := by
    simpa only [flipBoolWordAt_involutive] using hw
  have hopposite :=
    loss_translated_blocker_bit_opposite
      C exponent hexp honeLoss hv hcv hvw hsource hdest
  exact ⟨v, hv, w, hvw, c, hcv, hcw, hopposite, hword, hw⟩

theorem activeChoice_translatedLossCoveredWord_has_opposite_bits
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hn : 1 ≤ n)
    {word : Fin n → Bool}
    (hcovered :
      word ∈ translatedLossCoveredWords C exponent
        (projectedLossActiveFlipChoice C exponent hexp hn)) :
    ∃ v ∈ projectedLossVertices C exponent,
      ∃ w : V, v ≠ w ∧
        ∃ c : Fin n,
          c ∈ retainedActive C v ∧
          c ∈ retainedActive C w ∧
          retainedBit C w c = !(retainedBit C v c) ∧
          word ∈ translatedCompletionWords C v c ∧
          word ∈ retainedCompletionWords C w :=
  translatedLossCoveredWord_has_opposite_active_bits
    C exponent hexp honeLoss
    (projectedLossActiveFlipChoice C exponent hexp hn)
    (fun v hv =>
      projectedLossActiveFlipChoice_mem_retainedActive
        C exponent hexp hn hv)
    hcovered

#print axioms translatedLossCoveredWord_has_opposite_active_bits
#print axioms activeChoice_translatedLossCoveredWord_has_opposite_bits

end OrderedEdgeColoring
end JSP000404Research
