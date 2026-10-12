import JSP000404Research.ResidualActualCollisionTwoBitDisagreement
import JSP000404Research.ResidualIncomparableBridgePool
import Mathlib.Tactic

/-!
# Filter out all bridge faces whose canonical retained codes differ at <2 bits

This pool is STRICTER BY DEFINITION than the palette-incomparable
potential bridge family: besides mutually non-contained retained
active palettes, the two bridge endpoints must have Hamming bit
disagreement >=2.

A genuine collision between the two already globally injective
hard-word transports satisfies BOTH restrictions, as proved
in the previous modules. Hence every actual net-unpaid transport
image collision still lies in the newly filtered union.

The full dyadic mass of this potential pool is exact, using
pairwise disjoint overlap faces of distinct SOFT residual carriers.
The filtered mass is an honest covered-word bound, not a true-hole
or unreserved-surplus claim.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def twoBitDisagreementBridgeCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (incomparableBridgeSoftCarriers C exponent).filter
    (fun r =>
      2 ≤ (retainedBitDisagreementCoords C r.1 r.2).card)

noncomputable def twoBitDisagreementBridgeWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (twoBitDisagreementBridgeCarriers C exponent).biUnion
    (carrierOverlapWords C)

/-- The new candidate word pool is contained in the previous
incomparable-palette soft bridge pool. -/
theorem two_bit_bridge_words_subset_incomparable
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    twoBitDisagreementBridgeWords C exponent ⊆
      incomparableBridgeSoftWords C exponent := by
  classical
  intro word hw
  obtain ⟨r, hr, hrw⟩ := Finset.mem_biUnion.mp hw
  have hinc :=
    (Finset.mem_filter.mp hr).1
  exact Finset.mem_biUnion.mpr ⟨r,hinc,hrw⟩

/-- ALL actual full-forward/reverse hard-word sink collisions,
independent of profile-surplus reservations, have a UNIQUE soft
bridge owner whose canonical retained-code Hamming distance >=2. -/
theorem actual_collision_subset_two_bit_bridge_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    actualForwardReverseCollisionWords C exponent hexp honeLoss ⊆
      twoBitDisagreementBridgeWords C exponent := by
  classical
  intro word hw
  have hf := (Finset.mem_inter.mp hw).1
  have hr := (Finset.mem_inter.mp hw).2
  unfold forwardHardTransportSinkWords at hf
  unfold reverseStrictRigidSinkWords at hr
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hf
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hr
  have hcollision :
      (transportableHardWordToSingletonOrSoft C x).1 =
      (strictDescentRigidWordToSingletonOrSoft
        C exponent hexp honeLoss y).1 := hx.trans hy.symm
  let p := transportableWordCarrier C x
  let q := strictDescentRigidWordCarrier C exponent y
  have howner :=
    forward_reverse_sink_collision_has_bridge_soft_owner
      C exponent hexp honeLoss x y hcollision
  change (q.1.1, p.1.2) ∈ softOverlapCarrierPairs C ∧
    (transportableHardWordToSingletonOrSoft C x).1 ∈
      carrierOverlapWords C (q.1.1, p.1.2) at howner
  have hp : p.1 ∈ transportableHardOverlapCarrierPairs C := p.2
  have hq : q.1 ∈ netStrictDescentRigidCarriers C exponent := q.2
  have hcandidate :
      (q.1.1, p.1.2) ∈
        forwardReverseBridgeSoftCarriers C exponent := by
    change (q.1.1, p.1.2) ∈
      (softOverlapCarrierPairs C).filter _
    apply Finset.mem_filter.mpr
    exact ⟨howner.1, ⟨p.1,hp,q.1,hq,rfl,rfl⟩⟩
  have hpalette :=
    forward_reverse_collision_bridge_active_incomparable
      C exponent hexp honeLoss x y hcollision
  change ¬ retainedActive C q.1.1 ⊆ retainedActive C p.1.2 ∧
    ¬ retainedActive C p.1.2 ⊆ retainedActive C q.1.1 at hpalette
  have hbits :=
    forward_reverse_actual_collision_bridge_hamming_ge_two
      C exponent hexp honeLoss x y hcollision
  change 2 ≤ (retainedBitDisagreementCoords
    C q.1.1 p.1.2).card at hbits
  apply Finset.mem_biUnion.mpr
  refine ⟨(q.1.1, p.1.2), ?_, ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hcandidate, hpalette⟩, hbits⟩
  · rw [← hx]
    exact howner.2

/-- The ACTUAL net-unpaid collision subset inherits the sharper
two-bit bridge restriction. -/
theorem net_actual_collision_subset_two_bit_bridge_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netActualForwardReverseCollisionWords
        C exponent hexp honeLoss ⊆
      twoBitDisagreementBridgeWords C exponent :=
  (net_actual_collision_subset_all_actual
    C exponent hexp honeLoss).trans
      (actual_collision_subset_two_bit_bridge_words
        C exponent hexp honeLoss)

/-- The doubly filtered SOFT faces still admit an exact,
non-overlapping dyadic carrier mass count. -/
theorem two_bit_bridge_words_card_eq_dyadic_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (twoBitDisagreementBridgeWords C exponent).card =
      ∑ r ∈ twoBitDisagreementBridgeCarriers C exponent,
        2 ^ (commonRetainedInactive C r.1 r.2).card := by
  classical
  have hpair :
      ((twoBitDisagreementBridgeCarriers C exponent : Finset (V × V)) :
        Set (V × V)).PairwiseDisjoint (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply overlapCarrierWords_pairwiseDisjoint C
    · have hp' : p ∈ twoBitDisagreementBridgeCarriers C exponent := by
        simpa using hp
      have hinc := (Finset.mem_filter.mp hp').1
      have hbridge := (Finset.mem_filter.mp hinc).1
      have hsoft := (Finset.mem_filter.mp hbridge).1
      exact ((mem_softOverlapCarrierPairs C p).1 hsoft).1
    · have hq' : q ∈ twoBitDisagreementBridgeCarriers C exponent := by
        simpa using hq
      have hinc := (Finset.mem_filter.mp hq').1
      have hbridge := (Finset.mem_filter.mp hinc).1
      have hsoft := (Finset.mem_filter.mp hbridge).1
      exact ((mem_softOverlapCarrierPairs C q).1 hsoft).1
    · exact hpq
  unfold twoBitDisagreementBridgeWords
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro r hr
  have hinc := (Finset.mem_filter.mp hr).1
  have hbridge := (Finset.mem_filter.mp hinc).1
  have hsoft : r ∈ softOverlapCarrierPairs C :=
    (Finset.mem_filter.mp hbridge).1
  have hcarrier : r ∈ overlapCarrierPairs C :=
    ((mem_softOverlapCarrierPairs C r).1 hsoft).1
  obtain ⟨word, hword⟩ :=
    ((mem_overlapCarrierPairs C r).1 hcarrier).2
  exact retainedCompletionWords_inter_card
    C (Finset.mem_inter.mp hword).1
      (Finset.mem_inter.mp hword).2

/-- Precise new upper bound: net-unpaid duplicated hard-transport
destinations can only lie in bridge cubes with both incomparable
active palettes AND at least two retained-bit disagreements. -/
theorem net_actual_collision_card_le_two_bit_bridge_mass
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netActualForwardReverseCollisionWords
      C exponent hexp honeLoss).card ≤
      ∑ r ∈ twoBitDisagreementBridgeCarriers C exponent,
        2 ^ (commonRetainedInactive C r.1 r.2).card := by
  rw [← two_bit_bridge_words_card_eq_dyadic_sum]
  exact Finset.card_le_card
    (net_actual_collision_subset_two_bit_bridge_words
      C exponent hexp honeLoss)

/-- The exact net-forward/reverse transport source-plus-unused-sink
identity yields a sharper covered-sink budget with ONLY doubly
filtered candidate soft bridge masses. -/
theorem net_mobile_mass_plus_unused_le_two_bit_bridge_dyadic
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netTransportableHardWords C exponent).card +
      (netStrictDescentRigidWords C exponent).card +
        (netMobileUnusedCoveredSinkWords
          C exponent hexp honeLoss).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card +
        (∑ r ∈ twoBitDisagreementBridgeCarriers C exponent,
          2 ^ (commonRetainedInactive C r.1 r.2).card) := by
  have hmass :=
    net_mobile_source_plus_unused_eq_covered_plus_actual
      C exponent hexp honeLoss
  have hbound :=
    net_actual_collision_card_le_two_bit_bridge_mass
      C exponent hexp honeLoss
  omega

/-- If every potential incomparable-palette bridge has Hamming
distance <=1, then the actual full-forward/reverse sink intersection
is EMPTY. This is conditional, not a fabricated global planar law. -/
theorem actual_collision_empty_of_incomparable_bridge_hamming_le_one
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hsmall :
      ∀ r ∈ incomparableBridgeSoftCarriers C exponent,
        (retainedBitDisagreementCoords C r.1 r.2).card ≤ 1) :
    actualForwardReverseCollisionWords C exponent hexp honeLoss = ∅ := by
  classical
  ext word
  constructor
  · intro hw
    have hmem :=
      actual_collision_subset_two_bit_bridge_words
        C exponent hexp honeLoss hw
    obtain ⟨r, hr, _⟩ := Finset.mem_biUnion.mp hmem
    have hf := Finset.mem_filter.mp hr
    have hle := hsmall r hf.1
    have hge := hf.2
    omega
  · intro hw
    simpa using hw

#print axioms two_bit_bridge_words_subset_incomparable
#print axioms actual_collision_subset_two_bit_bridge_words
#print axioms net_actual_collision_subset_two_bit_bridge_words
#print axioms two_bit_bridge_words_card_eq_dyadic_sum
#print axioms net_actual_collision_card_le_two_bit_bridge_mass
#print axioms net_mobile_mass_plus_unused_le_two_bit_bridge_dyadic
#print axioms actual_collision_empty_of_incomparable_bridge_hamming_le_one

end OrderedEdgeColoring
end JSP000404Research
