import JSP000404Research.ResidualLossBlockerEdge
import Mathlib.Tactic

/-!
# Triangular support of translated loss blocks

For a projected-loss vertex v, translating along an outgoing retained
coordinate can only meet completion cubes strictly to the right of v.
Translating along an incoming retained coordinate can only meet completion
cubes strictly to the left.

At v itself disjointness follows from active-coordinate flipping.  On the
wrong side, any common word would be a translated blocker, contradicting the
one-sided blocker theorem.

This gives an upper-/lower-triangular support pattern between translated loss
blocks and the original completion family.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translated_loss_outgoing_disjoint_completion_of_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcOut : c ∈ outgoingRetained C v)
    (hwv : w ≤ v) :
    Disjoint
      (translatedCompletionWords C v c)
      (retainedCompletionWords C w) := by
  classical
  rw [Finset.disjoint_left]
  intro word htrans hw
  have hvOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 htrans
  by_cases hwvEq : w = v
  · subst w
    exact flip_active_not_mem_completion
      C hvOrig hc
      (by
        simpa [flipBoolWordAt_involutive] using hw)
  · have hvw : v ≠ w := Ne.symm hwvEq
    have hvwlt :=
      loss_translated_blocker_right_of_outgoing
        C exponent hexp honeLoss
        hvLoss hvw hc hcOut hvOrig
        (by
          simpa [flipBoolWordAt_involutive] using hw)
    exact (not_lt_of_ge hwv) hvwlt

theorem translated_loss_incoming_disjoint_completion_of_ge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v w : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcIn : c ∈ incomingRetained C v)
    (hvw : v ≤ w) :
    Disjoint
      (translatedCompletionWords C v c)
      (retainedCompletionWords C w) := by
  classical
  rw [Finset.disjoint_left]
  intro word htrans hw
  have hvOrig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 htrans
  by_cases hvwEq : v = w
  · subst w
    exact flip_active_not_mem_completion
      C hvOrig hc
      (by
        simpa [flipBoolWordAt_involutive] using hw)
  · have hvwNe : v ≠ w := hvwEq
    have hwvlt :=
      loss_translated_blocker_left_of_incoming
        C exponent hexp honeLoss
        hvLoss hvwNe hc hcIn hvOrig
        (by
          simpa [flipBoolWordAt_involutive] using hw)
    exact (not_lt_of_ge hvw) hwvlt

theorem translated_loss_outgoing_subset_uncovered_prefix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcOut : c ∈ outgoingRetained C v) :
    ∀ {word : Fin n → Bool},
      word ∈ translatedCompletionWords C v c →
      ∀ w : V, w ≤ v →
        word ∉ retainedCompletionWords C w := by
  intro word hword w hwv hw
  exact Finset.disjoint_left.mp
    (translated_loss_outgoing_disjoint_completion_of_le
      C exponent hexp honeLoss hvLoss hc hcOut hwv)
    hword hw

theorem translated_loss_incoming_subset_uncovered_suffix
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    {v : V}
    (hvLoss : v ∈ projectedLossVertices C exponent)
    {c : Fin n}
    (hc : c ∈ retainedActive C v)
    (hcIn : c ∈ incomingRetained C v) :
    ∀ {word : Fin n → Bool},
      word ∈ translatedCompletionWords C v c →
      ∀ w : V, v ≤ w →
        word ∉ retainedCompletionWords C w := by
  intro word hword w hvw hw
  exact Finset.disjoint_left.mp
    (translated_loss_incoming_disjoint_completion_of_ge
      C exponent hexp honeLoss hvLoss hc hcIn hvw)
    hword hw

#print axioms translated_loss_outgoing_disjoint_completion_of_le
#print axioms translated_loss_incoming_disjoint_completion_of_ge
#print axioms translated_loss_outgoing_subset_uncovered_prefix
#print axioms translated_loss_incoming_subset_uncovered_suffix

end OrderedEdgeColoring
end JSP000404Research
