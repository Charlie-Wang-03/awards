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

#print axioms bridge_soft_subset_unused_strict_lower_words
#print axioms bridge_soft_card_le_unused_strict_lower_words

end OrderedEdgeColoring
end JSP000404Research
