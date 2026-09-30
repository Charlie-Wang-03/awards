import JSP000404Research.ResidualLossDirectionalWitness
import JSP000404Research.ResidualLossFibreRank
import Mathlib.Tactic

/-!
# Directed translated-loss fibres

If every projected-loss vertex chooses an outgoing retained coordinate, then
every word in every translated loss block is true at its owner coordinate:
the original completion word has canonical bit false there, and the
translation flips it to true.

Dually, an incoming choice makes every translated word false at its owner
coordinate.

Hence under a globally outgoing choice every translated-loss fibre is purely
the true prefix from the previous rank theorem; under a globally incoming
choice it is purely the false suffix.  The two-sided fibre obstruction
disappears completely.

A common top vertex lying strictly above every loss vertex supplies such a
global outgoing choice; a common bottom vertex supplies the incoming version.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem translated_loss_word_true_of_outgoing
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c : Fin n}
    (hcOut : c ∈ outgoingRetained C v)
    {word : Fin n → Bool}
    (hword : word ∈ translatedCompletionWords C v c) :
    word c = true := by
  have hcActive :=
    outgoingRetained_subset_retainedActive C v hcOut
  have horig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hword
  have hcomp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word c)).1 horig
  have hfalse :=
    retainedBit_false_of_outgoingRetained C hcOut
  have hat := hcomp c hcActive
  rw [flipBoolWordAt_at, hfalse] at hat
  cases h : word c <;> simp [h] at hat ⊢

theorem translated_loss_word_false_of_incoming
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {c : Fin n}
    (hcIn : c ∈ incomingRetained C v)
    {word : Fin n → Bool}
    (hword : word ∈ translatedCompletionWords C v c) :
    word c = false := by
  have hcActive :=
    incomingRetained_subset_retainedActive C v hcIn
  have horig :
      flipBoolWordAt word c ∈ retainedCompletionWords C v :=
    (mem_translatedCompletionWords C v c word).1 hword
  have hcomp :=
    (mem_retainedCompletionWords C v
      (flipBoolWordAt word c)).1 horig
  have htrue :=
    (mem_incomingRetained_iff_retainedBit_true C v c).1 hcIn
  have hat := hcomp c hcActive
  rw [flipBoolWordAt_at, htrue] at hat
  cases h : word c <;> simp [h] at hat ⊢

theorem outgoing_choice_translatedLossFibre_all_true
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (hchoice :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        choice v ∈ outgoingRetained C v)
    (word : Fin n → Bool) :
    ∀ v,
      v ∈ translatedLossFibre C exponent choice word →
      word (choice v) = true := by
  intro v hv
  have hvData :=
    (mem_translatedLossFibre
      C exponent choice word v).1 hv
  exact translated_loss_word_true_of_outgoing
    C (hchoice v hvData.1) hvData.2

theorem incoming_choice_translatedLossFibre_all_false
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (choice : V → Fin n)
    (hchoice :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        choice v ∈ incomingRetained C v)
    (word : Fin n → Bool) :
    ∀ v,
      v ∈ translatedLossFibre C exponent choice word →
      word (choice v) = false := by
  intro v hv
  have hvData :=
    (mem_translatedLossFibre
      C exponent choice word v).1 hv
  exact translated_loss_word_false_of_incoming
    C (hchoice v hvData.1) hvData.2

theorem exists_outgoing_loss_choice_of_common_top
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (hn : 0 < n)
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (top : V)
    (htop :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        v < top) :
    ∃ choice : V → Fin n,
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        choice v ∈ outgoingRetained C v ∧
        choice v ∈ retainedActive C v := by
  classical
  have hwit :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        ∃ c : Fin n,
          c ∈ outgoingRetained C v ∧
          c ∈ retainedActive C v := by
    intro v hv
    exact projectedLoss_outgoing_witness_of_lt
      C exponent hexp honeLoss hv (htop v hv)
  let choice : V → Fin n := fun v =>
    if hv : v ∈ projectedLossVertices C exponent then
      Classical.choose (hwit v hv)
    else
      ⟨0,hn⟩
  refine ⟨choice,?_⟩
  intro v hv
  dsimp [choice]
  rw [dif_pos hv]
  exact Classical.choose_spec (hwit v hv)

theorem exists_incoming_loss_choice_of_common_bottom
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (hn : 0 < n)
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss :
      ∀ v, (active C v).card ≤ n - exponent v + 1)
    (bottom : V)
    (hbottom :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        bottom < v) :
    ∃ choice : V → Fin n,
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        choice v ∈ incomingRetained C v ∧
        choice v ∈ retainedActive C v := by
  classical
  have hwit :
      ∀ v,
        v ∈ projectedLossVertices C exponent →
        ∃ c : Fin n,
          c ∈ incomingRetained C v ∧
          c ∈ retainedActive C v := by
    intro v hv
    exact projectedLoss_incoming_witness_of_lt
      C exponent hexp honeLoss hv (hbottom v hv)
  let choice : V → Fin n := fun v =>
    if hv : v ∈ projectedLossVertices C exponent then
      Classical.choose (hwit v hv)
    else
      ⟨0,hn⟩
  refine ⟨choice,?_⟩
  intro v hv
  dsimp [choice]
  rw [dif_pos hv]
  exact Classical.choose_spec (hwit v hv)

#print axioms translated_loss_word_true_of_outgoing
#print axioms translated_loss_word_false_of_incoming
#print axioms outgoing_choice_translatedLossFibre_all_true
#print axioms incoming_choice_translatedLossFibre_all_false
#print axioms exists_outgoing_loss_choice_of_common_top
#print axioms exists_incoming_loss_choice_of_common_bottom

end OrderedEdgeColoring
end JSP000404Research
