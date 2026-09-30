import JSP000404Research.ResidualCompletionAccounting
import JSP000404Research.ResidualPairLocalFlip
import Mathlib.Tactic

/-!
# Single-fibre Boolean displacement

A word with completion fibre of cardinality one is not yet a Boolean hole, but
it is the correct intermediate state in a global augmenting chain.

Suppose word is covered only by Q_v and c is active at v. Flipping c leaves
Q_v. Any new blocker must activate c; otherwise flipping back would show that
the original word was also covered by that blocker, contradicting uniqueness.
The blocker bit at c is the opposite of v's bit.

Since retained completion multiplicity is globally at most two, the flipped
word has fibre cardinality 0, 1, or 2. Thus every single-fibre step either
reaches a genuine hole or moves to another single/overlap state with a
controlled coordinate reversal.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

def IsSingleCompletionWord
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (v : V) (word : Fin n → Bool) : Prop :=
  word ∈ retainedCompletionWords C v ∧
  ∀ w : V,
    word ∈ retainedCompletionWords C w →
    w = v

theorem singleCompletion_fibre_eq_singleton
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    (hsingle : IsSingleCompletionWord C v word) :
    completionFibre C word = {v} := by
  classical
  ext w
  constructor
  · intro hw
    have hwComp :=
      (mem_completionFibre C word w).1 hw
    have hwv := hsingle.2 w hwComp
    subst w
    simp
  · intro hw
    have hwv : w = v := by simpa using hw
    subst w
    exact (mem_completionFibre C word v).2 hsingle.1

theorem singleCompletion_fibre_card_eq_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool}
    (hsingle : IsSingleCompletionWord C v word) :
    (completionFibre C word).card = 1 := by
  rw [singleCompletion_fibre_eq_singleton C hsingle]
  simp

theorem single_flip_blocker_active
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {word : Fin n → Bool} {c : Fin n}
    (hsingle : IsSingleCompletionWord C v word)
    (hc : c ∈ retainedActive C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    c ∈ retainedActive C w := by
  by_contra hcW
  have hwOrig :
      word ∈ retainedCompletionWords C w :=
    (mem_completion_iff_flip_of_inactive C hcW).1 hw
  have hwv := hsingle.2 w hwOrig
  subst w
  exact flip_active_not_mem_completion
    C hsingle.1 hc hw

theorem single_flip_blocker_ne_owner
    {V : Type*} [LinearOrder V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {word : Fin n → Bool} {c : Fin n}
    (hsingle : IsSingleCompletionWord C v word)
    (hc : c ∈ retainedActive C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    w ≠ v := by
  intro hwv
  subst w
  exact flip_active_not_mem_completion
    C hsingle.1 hc hw

theorem single_flip_blocker_bit_opposite
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v w : V} {word : Fin n → Bool} {c : Fin n}
    (hsingle : IsSingleCompletionWord C v word)
    (hc : c ∈ retainedActive C v)
    (hw :
      flipBoolWordAt word c ∈ retainedCompletionWords C w) :
    retainedBit C w c = !(retainedBit C v c) := by
  have hcW :=
    single_flip_blocker_active C hsingle hc hw
  have hvComp :=
    (mem_retainedCompletionWords C v word).1 hsingle.1
  have hwComp :=
    (mem_retainedCompletionWords C w
      (flipBoolWordAt word c)).1 hw
  have hvAt := hvComp c hc
  have hwAt := hwComp c hcW
  rw [flipBoolWordAt_at, hvAt] at hwAt
  exact hwAt.symm


theorem single_flip_fibre_trichotomy
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool} {c : Fin n}
    (hsingle : IsSingleCompletionWord C v word)
    (hc : c ∈ retainedActive C v) :
    let y := flipBoolWordAt word c
    (completionFibre C y).card = 0 ∨
    (completionFibre C y).card = 1 ∨
    (completionFibre C y).card = 2 := by
  dsimp
  have hle :=
    completionFibre_card_le_two C
      (flipBoolWordAt word c)
  omega

theorem single_flip_hole_or_controlled_blocker
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {v : V} {word : Fin n → Bool} {c : Fin n}
    (hsingle : IsSingleCompletionWord C v word)
    (hc : c ∈ retainedActive C v) :
    let y := flipBoolWordAt word c
    ((completionFibre C y).card = 0)
    ∨
    ((completionFibre C y).card = 1 ∨
      (completionFibre C y).card = 2) ∧
      ∀ w : V,
        y ∈ retainedCompletionWords C w →
        w ≠ v ∧
        c ∈ retainedActive C w ∧
        retainedBit C w c = !(retainedBit C v c) := by
  dsimp
  rcases single_flip_fibre_trichotomy C hsingle hc
    with hzero | hone | htwo
  · exact Or.inl hzero
  · right
    refine ⟨Or.inl hone, ?_⟩
    intro w hw
    exact ⟨single_flip_blocker_ne_owner C hsingle hc hw,
      single_flip_blocker_active C hsingle hc hw,
      single_flip_blocker_bit_opposite C hsingle hc hw⟩
  · right
    refine ⟨Or.inr htwo, ?_⟩
    intro w hw
    exact ⟨single_flip_blocker_ne_owner C hsingle hc hw,
      single_flip_blocker_active C hsingle hc hw,
      single_flip_blocker_bit_opposite C hsingle hc hw⟩

#print axioms singleCompletion_fibre_card_eq_one
#print axioms single_flip_blocker_active
#print axioms single_flip_blocker_bit_opposite
#print axioms single_flip_hole_or_controlled_blocker

end OrderedEdgeColoring
end JSP000404Research
