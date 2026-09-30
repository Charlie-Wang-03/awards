import JSP000404Research.ResidualSaturatedOverlapDecomposition
import JSP000404Research.ResidualUnsafeOverlapGlobalCard
import Mathlib.Tactic

/-!
# Safe/unsafe decomposition of the saturated--saturated hard remainder

Every overlap word has a unique ordered residual carrier.  For a
saturated--saturated hard word that carrier is either safe (has a retained
recolouring coordinate outside the residual forbidden set) or unsafe.

The unsafe part is contained in the global unsafe-overlap word set, whose
cardinality has already been reduced to a matching count.  This file packages
that decomposition explicitly so the all-cardinality hard-word proof can treat

* safe saturated words by displacement / recolouring, and
* unsafe saturated words by matching-type unit charging.

No cardinality restriction on the vertex set is used.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def unsafeSaturatedSaturatedOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) :=
  saturatedSaturatedOverlapWords C exponent ∩ unsafeOverlapWords C

noncomputable def safeSaturatedSaturatedOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Finset (Fin n → Bool) :=
  saturatedSaturatedOverlapWords C exponent \
    unsafeSaturatedSaturatedOverlapWords C exponent

theorem unsafeSaturatedSaturated_subset_unsafeOverlapWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    unsafeSaturatedSaturatedOverlapWords C exponent ⊆
      unsafeOverlapWords C := by
  intro word hword
  exact (Finset.mem_inter.mp hword).2

theorem unsafeSaturatedSaturated_two_mul_card_le
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    2 * (unsafeSaturatedSaturatedOverlapWords C exponent).card
      ≤ Fintype.card V := by
  have hcard :
      (unsafeSaturatedSaturatedOverlapWords C exponent).card ≤
        (unsafeOverlapWords C).card :=
    Finset.card_le_card
      (unsafeSaturatedSaturated_subset_unsafeOverlapWords C exponent)
  have hunsafe := unsafeOverlapWords_two_mul_card_le C
  omega

theorem safeSaturatedSaturated_card_add_unsafe_card_eq_saturatedSaturated
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (safeSaturatedSaturatedOverlapWords C exponent).card +
        (unsafeSaturatedSaturatedOverlapWords C exponent).card
      =
    (saturatedSaturatedOverlapWords C exponent).card := by
  classical
  unfold safeSaturatedSaturatedOverlapWords
  exact Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left)

#print axioms unsafeSaturatedSaturated_two_mul_card_le
#print axioms safeSaturatedSaturated_card_add_unsafe_card_eq_saturatedSaturated

end OrderedEdgeColoring
end JSP000404Research
