import JSP000404Research.ResidualBridgeStrictDyadicDescentGap
import Mathlib.Tactic

/-!
# Unused lower rigid cube capacity, with no double counting

The soft bridge pool is made of already-COVERED words. It is disjoint
from strict-rigid hard sources but lies in the same strict-rigid LOWER
completion cubes. Thus it is contained in the exact SET DIFFERENCE of
lower cubes minus reverse hard sources.

This gives a set-level, not merely cardinal, interpretation of the
strict lower-minus-upper dyadic gap. These unused *lower-cube slots*
are not necessarily true Boolean holes and are not unreserved global
profile surplus. No award-problem conclusion follows from this lemma.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def netStrictRigidUnusedLowerWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  netStrictRigidLowerCapacityWords C exponent \
    netStrictDescentRigidWords C exponent

/-- Every candidate bridge-soft collision word uses an unoccupied
slot of a strict-rigid lower cube, rather than a strict hard source
word. This is an exact word-level containment, not a hole payment. -/
theorem bridge_soft_subset_unused_strict_lower_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    forwardReverseBridgeSoftWords C exponent ⊆
      netStrictRigidUnusedLowerWords C exponent := by
  classical
  intro w hw
  change w ∈ netStrictRigidLowerCapacityWords C exponent \
    netStrictDescentRigidWords C exponent
  apply Finset.mem_sdiff.mpr
  constructor
  · exact forwardReverseBridgeSoftWords_subset_strict_lower_cubes C exponent hw
  · intro hrig
    exact (Finset.disjoint_left.mp
      (forwardReverseBridgeSoftWords_disjoint_strict_rigid_words C exponent))
      hw hrig

/-- Quantified bridge capacity in the *actual unused lower-cube
slots*. The right-hand set need not consist of Boolean holes. -/
theorem bridge_soft_card_le_unused_strict_lower_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (forwardReverseBridgeSoftWords C exponent).card ≤
      (netStrictRigidUnusedLowerWords C exponent).card := by
  exact Finset.card_le_card
    (bridge_soft_subset_unused_strict_lower_words C exponent)

/-- The exact count of unoccupied strict LOWER completion-cube slots
is the lower-target total minus the reverse strict-source upper-target
total. This is an identity of covered-cube slots, not of Boolean holes. -/
theorem unused_strict_lower_words_card_eq_dyadic_gap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netStrictRigidUnusedLowerWords C exponent).card =
      (∑ q ∈ netStrictDescentRigidCarriers C exponent,
        2 ^ exponent q.1) -
      (∑ q ∈ netStrictDescentRigidCarriers C exponent,
        2 ^ exponent q.2) := by
  classical
  change (netStrictRigidLowerCapacityWords C exponent \
    netStrictDescentRigidWords C exponent).card = _
  rw [Finset.card_sdiff_of_subset
    (netStrictDescentRigidWords_subset_strict_lower_cubes C exponent)]
  rw [netStrictRigidLowerCubes_card_eq_lower_target_sum
    C exponent hexp honeLoss]
  rw [netStrictDescentRigidWords_card_eq_upper_target_sum
    C exponent hexp honeLoss]

/-- Even the *unused* strict lower-cube slots remain globally COVERED:
every word in the lower-cube union extends a centre's retained code.
Consequently this capacity cannot, by itself, be allocated as holes. -/
theorem unused_strict_lower_words_subset_covered
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    netStrictRigidUnusedLowerWords C exponent ⊆
      coveredCompletionWords C := by
  classical
  intro word hword
  change word ∈ netStrictRigidLowerCapacityWords C exponent \
    netStrictDescentRigidWords C exponent at hword
  have hlower : word ∈ netStrictRigidLowerCapacityWords C exponent :=
    (Finset.mem_sdiff.mp hword).1
  change word ∈ (netStrictDescentRigidCarriers C exponent).biUnion
    (fun q => retainedCompletionWords C q.1) at hlower
  obtain ⟨q, _hq, hqword⟩ := Finset.mem_biUnion.mp hlower
  rw [coveredCompletionWords_eq_biUnion C]
  exact Finset.mem_biUnion.mpr
    ⟨q.1, Finset.mem_univ q.1, hqword⟩

/-- The potential bridge-soft collision pool's lower-cube slack is
DISJOINT from genuine Boolean holes, i.e. uncovered words.
Any global payment must therefore use a separate mechanism. -/
theorem unused_strict_lower_words_disjoint_true_holes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (netStrictRigidUnusedLowerWords C exponent)
      ((Finset.univ : Finset (Fin n → Bool)) \
        coveredCompletionWords C) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word hunused hhole
  exact (Finset.mem_sdiff.mp hhole).2
    (unused_strict_lower_words_subset_covered C exponent hunused)

#print axioms bridge_soft_subset_unused_strict_lower_words
#print axioms unused_strict_lower_words_subset_covered
#print axioms unused_strict_lower_words_disjoint_true_holes
#print axioms unused_strict_lower_words_card_eq_dyadic_gap
#print axioms bridge_soft_card_le_unused_strict_lower_words

end OrderedEdgeColoring
end JSP000404Research
