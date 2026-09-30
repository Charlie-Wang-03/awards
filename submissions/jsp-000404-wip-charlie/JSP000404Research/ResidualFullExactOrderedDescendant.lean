import JSP000404Research.ResidualTranslatedOverlapFullPair
import JSP000404Research.ResidualCommonInactiveSymmetry
import Mathlib.Tactic

/-!
# Order-normalized exact descendant from two full one-bit blockers

The pair-local one-bit branch already supplies a coordinate active at both
source endpoints.  Given two distinct exact full blockers, normalize their
residual-pair order while preserving the translated base word, inherited free
tensor, and nondecreasing overlap mass.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_two_full_exact_blockers_ordered_descendant
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hcu : c ∈ retainedActive C u)
    (hcv : c ∈ retainedActive C v)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z)
    (hwExact : ExactProjectedBudget C exponent w)
    (hzExact : ExactProjectedBudget C exponent z) :
    ∃ a b : V,
      a < b ∧
      IsResidual C a b ∧
      flipBoolWordAt base c ∈ retainedCompletionWords C a ∧
      flipBoolWordAt base c ∈ retainedCompletionWords C b ∧
      ExactProjectedBudget C exponent a ∧
      ExactProjectedBudget C exponent b ∧
      commonInactiveRetained C u v ⊆
        commonInactiveRetained C a b ∧
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card ≤
        (retainedCompletionWords C a ∩
          retainedCompletionWords C b).card := by
  have hyW :=
    oneFlip_fullBlocker_contains_base C hbase hw
  have hyZ :=
    oneFlip_fullBlocker_contains_base C hbase hz
  have hfree :=
    oneFlip_two_fullBlockers_inherit_commonInactive
      C hbase hcu hw hz
  have hmass :=
    oneFlip_source_overlap_card_le_two_fullBlocker_intersection
      C hw hz
  rcases oneFlip_two_fullBlockers_form_residual_pair
      C hbase hw hz hwz
    with hwzRes | hzwRes
  · exact ⟨w,z,hwzRes.1,hwzRes.2,
      hyW,hyZ,hwExact,hzExact,hfree,hmass⟩
  · have hfree' :
        commonInactiveRetained C u v ⊆
          commonInactiveRetained C z w := by
      intro e he
      have heWZ := hfree he
      rw [commonInactiveRetained_comm C w z] at heWZ
      exact heWZ
    have hmass' :
        (retainedCompletionWords C u ∩
          retainedCompletionWords C v).card ≤
        (retainedCompletionWords C z ∩
          retainedCompletionWords C w).card := by
      simpa [Finset.inter_comm] using hmass
    exact ⟨z,w,hzwRes.1,hzwRes.2,
      hyZ,hyW,hzExact,hwExact,hfree',hmass'⟩

#print axioms oneFlip_two_full_exact_blockers_ordered_descendant

end OrderedEdgeColoring
end JSP000404Research
