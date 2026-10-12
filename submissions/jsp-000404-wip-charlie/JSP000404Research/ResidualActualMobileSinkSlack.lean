import JSP000404Research.ResidualActualBridgeCollisionLedger
import Mathlib.Tactic

/-!
# Exact global conservation of mobile source, actual cross-collisions,
# unused covered sinks and unrealized bridge candidates

The earlier mobile-hard inequality replaced the actual cross-map image
intersection by an entire hypothetical bridge pool and discarded unused
singleton-or-soft sink capacity.

We now expose BOTH discarded terms as literal finite sets.

Let F and R be the exact forward/reverse sink images;
S be singleton-covered words; T be soft-overlap words; I=F∩R.
Write E=(S∪T)\(F∪R) for UNUSED eligible covered sinks,
and B\I for candidate bridge words which DO NOT actually collide.

Then, under the existing one-layer budget:

  |forward source| + |reverse source| + |E|
    = |S| + |T| + |I|,

  |forward source| + |reverse source| + |E| + |B\I|
    = |S| + |T| + |B|.

This is exact; the old candidate-bridge inequality is obtained by
discarding two NONNEGATIVE slack terms. Every set here is COVERED.
This does NOT prove the missing payment from true holes or profile
surplus and does NOT remove the sole WIP sorry.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A completion word cannot have both a unique covering vertex and
a soft residual overlap (which requires two covering vertices). -/
theorem singleton_soft_overlap_disjoint_global
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1)) :
    Disjoint (singletonCompletionWords C)
      (softOverlapCompletionWords C) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word hs ht
  have hone : (completionFibre C word).card = 1 :=
    (mem_singletonCompletionWords C word).1 hs
  have hoverlap : word ∈ overlapCompletionWords C := by
    rw [overlapCompletionWords_eq_hard_union_soft C]
    exact Finset.mem_union.mpr (Or.inr ht)
  have htwo : (completionFibre C word).card = 2 :=
    (mem_overlapCompletionWords C word).1 hoverlap
  omega

/-- All available covered sinks that were NOT actually consumed by
either of the two globally injective hard-source maps. -/
noncomputable def mobileUnusedCoveredSinkWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) :=
  (singletonCompletionWords C ∪ softOverlapCompletionWords C) \
    (forwardHardTransportSinkWords C ∪
      reverseStrictRigidSinkWords C exponent hexp honeLoss)

/-- No actually used forward or reverse sink is present in the
unused eligible covered-sink reservoir. -/
theorem mobile_unused_covered_sinks_disjoint_used
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Disjoint (mobileUnusedCoveredSinkWords C exponent hexp honeLoss)
      (forwardHardTransportSinkWords C ∪
        reverseStrictRigidSinkWords C exponent hexp honeLoss) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word hunused hused
  exact (Finset.mem_sdiff.mp hunused).2 hused

/-- True source-image conservation, with the exact unused covered
sink reserve retained instead of discarded. -/
theorem mobile_source_plus_unused_eligible_eq_covered_plus_actual
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card +
        (mobileUnusedCoveredSinkWords
          C exponent hexp honeLoss).card =
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
          (actualForwardReverseCollisionWords
            C exponent hexp honeLoss).card := by
  classical
  have hsub :=
    forward_reverse_sink_union_subset_singleton_soft
      C exponent hexp honeLoss
  have hdiff := Finset.card_sdiff_of_subset hsub
  change (mobileUnusedCoveredSinkWords C exponent hexp honeLoss).card =
    (singletonCompletionWords C ∪ softOverlapCompletionWords C).card -
    (forwardHardTransportSinkWords C ∪
      reverseStrictRigidSinkWords C exponent hexp honeLoss).card
    at hdiff
  have hle := Finset.card_le_card hsub
  have htotal :=
    Finset.card_union_of_disjoint (singleton_soft_overlap_disjoint_global C)
  have hsource :=
    forward_reverse_source_mass_eq_sink_union_add_actual_collisions
      C exponent hexp honeLoss
  omega

/-- EXACT decomposition of the potential-bridge budget's
overestimation into TWO independently checkable positive slacks:
unused singleton/soft sink words and hypothetical noncolliding bridge
words. There is no hidden multiset double-counting. -/
theorem mobile_source_plus_two_slacks_eq_coarse_bridge_budget
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (transportableHardOverlapCompletionWords C).card +
      (netStrictDescentRigidWords C exponent).card +
        (mobileUnusedCoveredSinkWords
          C exponent hexp honeLoss).card +
        (unusedCandidateBridgeWords
          C exponent hexp honeLoss).card =
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
          (forwardReverseBridgeSoftWords C exponent).card := by
  have hreal :=
    mobile_source_plus_unused_eligible_eq_covered_plus_actual
      C exponent hexp honeLoss
  have hpotential :=
    candidate_bridge_card_eq_actual_plus_unused
      C exponent hexp honeLoss
  omega

#print axioms singleton_soft_overlap_disjoint_global
#print axioms mobile_unused_covered_sinks_disjoint_used
#print axioms mobile_source_plus_unused_eligible_eq_covered_plus_actual
#print axioms mobile_source_plus_two_slacks_eq_coarse_bridge_budget

end OrderedEdgeColoring
end JSP000404Research
