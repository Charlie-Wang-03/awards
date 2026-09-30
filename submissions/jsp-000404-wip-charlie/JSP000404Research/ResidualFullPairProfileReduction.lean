import JSP000404Research.ResidualTranslatedOverlapFullPair
import JSP000404Research.ResidualLargeBlockerProfile
import Mathlib.Tactic

/-!
# Profile reduction of a two-full-blocker branch

Two distinct full blockers already form a residual pair and inherit the source
common-inactive set.  Apply the one-layer projected-profile trichotomy to both
blockers.

Unless one blocker is strict or one blocker is projected-loss, both blockers
are exact projected-budget vertices.  Hence the only genuinely lossless
recursive full branch is an exact--exact residual pair with inherited free set
and nondecreasing overlap mass.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

theorem oneFlip_two_fullBlockers_strict_or_loss_or_exact_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v w z : V} {c : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hw : w ∈ oneFlipFullBlockers C u v c)
    (hz : z ∈ oneFlipFullBlockers C u v c)
    (hwz : w ≠ z) :
    (
      exponent w < projectedFree C w
      ∨ exponent z < projectedFree C z
    )
    ∨
    (
      w ∈ projectedLossVertices C exponent
      ∨ z ∈ projectedLossVertices C exponent
    )
    ∨
    (
      ExactProjectedBudget C exponent w ∧
      ExactProjectedBudget C exponent z ∧
      ((w < z ∧ IsResidual C w z) ∨
        (z < w ∧ IsResidual C z w)) ∧
      commonInactiveRetained C u v ⊆
        commonInactiveRetained C w z ∧
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card ≤
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z).card
    ) := by
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
    with hwStrict | hwExact | hwLoss
  · exact Or.inl (Or.inl hwStrict)
  · rcases projectedProfile_strict_exact_or_loss
        C exponent hexp honeLoss z
      with hzStrict | hzExact | hzLoss
    · exact Or.inl (Or.inr hzStrict)
    · right
      right
      exact ⟨hwExact,hzExact,
        oneFlip_two_fullBlockers_form_residual_pair
          C hbase hw hz hwz,
        oneFlip_two_fullBlockers_inherit_commonInactive
          C hbase hc hw hz,
        oneFlip_source_overlap_card_le_two_fullBlocker_intersection
          C hw hz⟩
    · exact Or.inr (Or.inl (Or.inr hzLoss))
  · exact Or.inr (Or.inl (Or.inl hwLoss))

theorem twoFlip_two_fullBlockers_strict_or_loss_or_exact_pair
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss :
      ∀ x, (active C x).card ≤ n - exponent x + 1)
    {u v w z : V} {c d : Fin n}
    {base : Fin n → Bool}
    (hbase :
      base ∈ retainedCompletionWords C u ∩
        retainedCompletionWords C v)
    (hc : c ∈ retainedActive C u)
    (hd : d ∈ retainedActive C v)
    (hw : w ∈ twoFlipFullBlockers C u v c d)
    (hz : z ∈ twoFlipFullBlockers C u v c d)
    (hwz : w ≠ z) :
    (
      exponent w < projectedFree C w
      ∨ exponent z < projectedFree C z
    )
    ∨
    (
      w ∈ projectedLossVertices C exponent
      ∨ z ∈ projectedLossVertices C exponent
    )
    ∨
    (
      ExactProjectedBudget C exponent w ∧
      ExactProjectedBudget C exponent z ∧
      ((w < z ∧ IsResidual C w z) ∨
        (z < w ∧ IsResidual C z w)) ∧
      commonInactiveRetained C u v ⊆
        commonInactiveRetained C w z ∧
      (retainedCompletionWords C u ∩
        retainedCompletionWords C v).card ≤
        (retainedCompletionWords C w ∩
          retainedCompletionWords C z).card
    ) := by
  rcases projectedProfile_strict_exact_or_loss
      C exponent hexp honeLoss w
    with hwStrict | hwExact | hwLoss
  · exact Or.inl (Or.inl hwStrict)
  · rcases projectedProfile_strict_exact_or_loss
        C exponent hexp honeLoss z
      with hzStrict | hzExact | hzLoss
    · exact Or.inl (Or.inr hzStrict)
    · right
      right
      exact ⟨hwExact,hzExact,
        twoFlip_two_fullBlockers_form_residual_pair
          C hbase hw hz hwz,
        twoFlip_two_fullBlockers_inherit_commonInactive
          C hbase hc hd hw hz,
        twoFlip_source_overlap_card_le_two_fullBlocker_intersection
          C hw hz⟩
    · exact Or.inr (Or.inl (Or.inr hzLoss))
  · exact Or.inr (Or.inl (Or.inl hwLoss))

#print axioms oneFlip_two_fullBlockers_strict_or_loss_or_exact_pair
#print axioms twoFlip_two_fullBlockers_strict_or_loss_or_exact_pair

end OrderedEdgeColoring
end JSP000404Research
