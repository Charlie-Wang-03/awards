import JSP000404Research.ResidualActualMobileSinkSlack
import Mathlib.Tactic

/-!
# Net-unpaid EXACT forward/reverse mobile-source image accounting

Previous exact-image accounting used ALL forward-transportable hard
source words. Some of those faces were ALREADY PAID by profile surplus
and are not part of the final six-source geometric debt.

This module restricts the forward map to the actual NET UNPAID
transportable-hard word set. The original source map is injective,
so this restriction is still globally injective. Its exact image
intersection with the full reverse strict-rigid sink set is a
subfamily of the canonical bridge pool and of the earlier all-forward
actual intersection.

The resulting exact conservation identity therefore matches the TWO
actual unpaid mobile-hard families appearing in the sole WIP payment
obligation, without re-introducing previously reserved hard words:

  netForwardMass + reverseStrictMass + unusedEligibleSinkMass
    = singletonMass + softMass + NET_ACTUAL_CROSS_COLLISIONS.

This is a reduction in duplicated-payment bookkeeping, NOT a true
Boolean-hole or unused profile-surplus allocation.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def netForwardHardTransportSinkWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.image
    (fun x : {word : Fin n → Bool //
        word ∈ netTransportableHardWords C exponent} =>
      (transportableHardWordToSingletonOrSoft C
        ⟨x.1, netTransportableHardWords_subset_transportable
          C exponent x.2⟩).1)

/-- Forward map restricted to NET UNPAID hard sources remains a
global injection, with exactly the net source cardinality. -/
theorem netForwardHardTransportSinkWords_card
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (netForwardHardTransportSinkWords C exponent).card =
      (netTransportableHardWords C exponent).card := by
  classical
  have hinj : Function.Injective
    (fun x : {word : Fin n → Bool //
        word ∈ netTransportableHardWords C exponent} =>
      (transportableHardWordToSingletonOrSoft C
        ⟨x.1, netTransportableHardWords_subset_transportable
          C exponent x.2⟩).1) := by
    intro x y h
    have heq :
        transportableHardWordToSingletonOrSoft C
          ⟨x.1, netTransportableHardWords_subset_transportable
            C exponent x.2⟩ =
        transportableHardWordToSingletonOrSoft C
          ⟨y.1, netTransportableHardWords_subset_transportable
            C exponent y.2⟩ := Subtype.ext h
    have hinj' :=
      transportableHardWordToSingletonOrSoft_injective C heq
    have hval : x.1 = y.1 :=
      congrArg
        (fun z : {word : Fin n → Bool //
          word ∈ transportableHardOverlapCompletionWords C} => z.1)
        hinj'
    exact Subtype.ext hval
  unfold netForwardHardTransportSinkWords
  rw [Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_coe]

/-- There is no new forward transport algorithm: the net image
is a literal subset of the previously verified full forward image. -/
theorem netForwardHardTransportSinkWords_subset_forward
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    netForwardHardTransportSinkWords C exponent ⊆
      forwardHardTransportSinkWords C := by
  classical
  intro word hw
  unfold netForwardHardTransportSinkWords at hw
  obtain ⟨x, _hx, hx⟩ := Finset.mem_image.mp hw
  unfold forwardHardTransportSinkWords
  exact Finset.mem_image.mpr
    ⟨(⟨x.1, netTransportableHardWords_subset_transportable
        C exponent x.2⟩ :
        {word : Fin n → Bool //
          word ∈ transportableHardOverlapCompletionWords C}),
      Finset.mem_univ _, hx⟩

noncomputable def netActualForwardReverseCollisionWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) :=
  netForwardHardTransportSinkWords C exponent ∩
    reverseStrictRigidSinkWords C exponent hexp honeLoss

/-- Actual NET cross-direction collisions are only a subset of the
previous ALL-transportable collision set, which itself was a proper
subfamily of possible bridge words. -/
theorem net_actual_collision_subset_all_actual
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netActualForwardReverseCollisionWords C exponent hexp honeLoss ⊆
      actualForwardReverseCollisionWords C exponent hexp honeLoss := by
  intro word hw
  exact Finset.mem_inter.mpr
    ⟨netForwardHardTransportSinkWords_subset_forward
      C exponent (Finset.mem_inter.mp hw).1,
      (Finset.mem_inter.mp hw).2⟩

theorem net_actual_collision_subset_candidate_bridge
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netActualForwardReverseCollisionWords C exponent hexp honeLoss ⊆
      forwardReverseBridgeSoftWords C exponent :=
  (net_actual_collision_subset_all_actual
    C exponent hexp honeLoss).trans
      (actual_collision_subset_candidate_bridge
        C exponent hexp honeLoss)

/-- Exact net-unpaid mobile hard mass; original paid hard faces no
longer occur in the forward source term or its image. -/
theorem net_mobile_source_eq_sink_union_plus_actual_collision
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card =
        (netForwardHardTransportSinkWords C exponent ∪
          reverseStrictRigidSinkWords C exponent hexp honeLoss).card +
          (netActualForwardReverseCollisionWords
            C exponent hexp honeLoss).card := by
  have hf := netForwardHardTransportSinkWords_card C exponent
  have hr := reverseStrictRigidSinkWords_card
    C exponent hexp honeLoss
  have heq := Finset.card_union_add_card_inter
    (netForwardHardTransportSinkWords C exponent)
    (reverseStrictRigidSinkWords C exponent hexp honeLoss)
  change _ + _ = _ +
    (netForwardHardTransportSinkWords C exponent ∩
      reverseStrictRigidSinkWords C exponent hexp honeLoss).card
  omega

/-- The NET union also lands in singleton or soft-covered sink
words; forward images from already-paid sources play no role. -/
theorem net_mobile_sink_union_subset_singleton_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netForwardHardTransportSinkWords C exponent ∪
      reverseStrictRigidSinkWords C exponent hexp honeLoss ⊆
        singletonCompletionWords C ∪
          softOverlapCompletionWords C := by
  intro word hw
  have hfull :
      word ∈ forwardHardTransportSinkWords C ∪
        reverseStrictRigidSinkWords C exponent hexp honeLoss := by
    rcases Finset.mem_union.mp hw with hf | hr
    · exact Finset.mem_union.mpr
        (Or.inl (netForwardHardTransportSinkWords_subset_forward
          C exponent hf))
    · exact Finset.mem_union.mpr (Or.inr hr)
  exact forward_reverse_sink_union_subset_singleton_soft
    C exponent hexp honeLoss hfull

/-- Net-specific covered sink reserve, excluding only actually
used destinations of UNPAID forward and reverse sources. -/
noncomputable def netMobileUnusedCoveredSinkWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    Finset (Fin n → Bool) :=
  (singletonCompletionWords C ∪ softOverlapCompletionWords C) \
    (netForwardHardTransportSinkWords C exponent ∪
      reverseStrictRigidSinkWords C exponent hexp honeLoss)

/-- Final NET mobile-hard conservation exactly matches both mobile
source terms of the six-source admitted payment. The unused sink
terms are still already COVERED, not true holes. -/
theorem net_mobile_source_plus_unused_eq_covered_plus_actual
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card +
        (netMobileUnusedCoveredSinkWords
          C exponent hexp honeLoss).card =
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
          (netActualForwardReverseCollisionWords
            C exponent hexp honeLoss).card := by
  classical
  have hsub :=
    net_mobile_sink_union_subset_singleton_soft
      C exponent hexp honeLoss
  have hdiff := Finset.card_sdiff_of_subset hsub
  change (netMobileUnusedCoveredSinkWords
      C exponent hexp honeLoss).card =
    (singletonCompletionWords C ∪ softOverlapCompletionWords C).card -
    (netForwardHardTransportSinkWords C exponent ∪
      reverseStrictRigidSinkWords C exponent hexp honeLoss).card
    at hdiff
  have hle := Finset.card_le_card hsub
  have htotal :=
    Finset.card_union_of_disjoint (singleton_soft_overlap_disjoint_global C)
  have hsource :=
    net_mobile_source_eq_sink_union_plus_actual_collision
      C exponent hexp honeLoss
  omega


/-- Formally equivalent reformulation of ANY proposed global payment
for the two NET unpaid mobile hard classes.

All further debts (including soft overlap, rigid twins, the two
mixed-rigid branches, and projected loss) can be put into 'otherDebt'.
The genuine true-hole / unreserved-surplus capacity is the arbitrary
'availableBudget'.

The REFORMULATED payment includes ONLY the actual intersection of
net forward/reverse transport images, and CREDIT from covered
singleton/soft destination words not consumed by either transport.

This theorem does NOT assert either side without a geometric proof.
The equivalence does not make the original lower-branch conjecture
true. It identifies a sharper possible shape for the ONE open input. -/
theorem net_mobile_payment_iff_actual_collision_unused_sink_credit
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (otherDebt availableBudget : ℕ) :
    (otherDebt +
      (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card ≤ availableBudget) ↔
    (otherDebt +
      (singletonCompletionWords C).card +
      (softOverlapCompletionWords C).card +
      (netActualForwardReverseCollisionWords
        C exponent hexp honeLoss).card ≤
      availableBudget +
        (netMobileUnusedCoveredSinkWords
          C exponent hexp honeLoss).card) := by
  have hnet :=
    net_mobile_source_plus_unused_eq_covered_plus_actual
      C exponent hexp honeLoss
  omega

#print axioms netForwardHardTransportSinkWords_card
#print axioms net_mobile_payment_iff_actual_collision_unused_sink_credit
#print axioms netForwardHardTransportSinkWords_subset_forward
#print axioms net_actual_collision_subset_all_actual
#print axioms net_actual_collision_subset_candidate_bridge
#print axioms net_mobile_source_eq_sink_union_plus_actual_collision
#print axioms net_mobile_sink_union_subset_singleton_soft
#print axioms net_mobile_source_plus_unused_eq_covered_plus_actual

end OrderedEdgeColoring
end JSP000404Research
