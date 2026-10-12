import JSP000404Research.ResidualActualCollisionCrossActive
import Mathlib.Tactic

/-!
# Eliminate all comparable-palette candidate soft bridges

The previous candidate bridge-soft pool included whole soft overlap
faces (b,v) for reverse-strict lower b and forward-mobile upper v.
Actual cross-image collisions FORCE incomparable retained-active
sets at b,v; all candidate faces whose endpoint palettes are nested
are categorically incapable of collision.

Filter the original finite bridge carrier family by the exact,
coordinatewise necessary active-palette obstruction. Unlike the old
bridge pool, this refined pool excludes every comparable-palette face.
No new geometry assumptions or guessed hole allocations are involved.

The refined pool is a subset of the old candidate pool, contains the
actual full-forward and NET-unpaid forward/reverse collisions, and
has an exact conditional emptiness corollary when all candidate
bridge endpoints happen to have comparable active palettes.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

noncomputable def incomparableBridgeSoftCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) := by
  classical
  exact (forwardReverseBridgeSoftCarriers C exponent).filter fun r =>
    ¬ retainedActive C r.1 ⊆ retainedActive C r.2 ∧
      ¬ retainedActive C r.2 ⊆ retainedActive C r.1

noncomputable def incomparableBridgeSoftWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (incomparableBridgeSoftCarriers C exponent).biUnion
    (carrierOverlapWords C)

/-- The active-palette filter never introduces a candidate bridge
outside the original oriented soft-bridge carrier family. -/
theorem incomparable_bridge_soft_words_subset_candidate
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    incomparableBridgeSoftWords C exponent ⊆
      forwardReverseBridgeSoftWords C exponent := by
  classical
  intro word hw
  obtain ⟨r, hr, hrw⟩ := Finset.mem_biUnion.mp hw
  have hcandidate : r ∈ forwardReverseBridgeSoftCarriers C exponent :=
    (Finset.mem_filter.mp hr).1
  exact Finset.mem_biUnion.mpr ⟨r, hcandidate, hrw⟩

/-- Every ACTUAL full-forward/reverse collision has a soft bridge
whose retained active endpoints are incomparable. -/
theorem actual_collision_subset_incomparable_bridge_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    actualForwardReverseCollisionWords C exponent hexp honeLoss ⊆
      incomparableBridgeSoftWords C exponent := by
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
    exact ⟨howner.1, ⟨p.1, hp, q.1, hq, rfl, rfl⟩⟩
  have hpalette :=
    forward_reverse_collision_bridge_active_incomparable
      C exponent hexp honeLoss x y hcollision
  change ¬ retainedActive C q.1.1 ⊆ retainedActive C p.1.2 ∧
    ¬ retainedActive C p.1.2 ⊆ retainedActive C q.1.1 at hpalette
  apply Finset.mem_biUnion.mpr
  refine ⟨(q.1.1, p.1.2), ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hcandidate, hpalette⟩
  · rw [← hx]
    exact howner.2

/-- In particular, every collision from the genuine NET UNPAID
forward hard source is restricted to the smaller filtered pool. -/
theorem net_actual_collision_subset_incomparable_bridge_words
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    netActualForwardReverseCollisionWords C exponent hexp honeLoss ⊆
      incomparableBridgeSoftWords C exponent :=
  (net_actual_collision_subset_all_actual
    C exponent hexp honeLoss).trans
      (actual_collision_subset_incomparable_bridge_words
        C exponent hexp honeLoss)

/-- The strict, independently checkable candidate bridge bound
charges no possible collision to a comparable-palette carrier. -/
theorem net_actual_collision_card_le_incomparable_bridge_mass
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1) :
    (netActualForwardReverseCollisionWords
      C exponent hexp honeLoss).card ≤
      (incomparableBridgeSoftWords C exponent).card :=
  Finset.card_le_card
    (net_actual_collision_subset_incomparable_bridge_words
      C exponent hexp honeLoss)

/-- If every geometrically candidate bridge has NESTED
retained-active palettes, then no actual collision is possible.
This is conditional on a genuine palette property, not an
unproved assertion that all planar AngleCap bridges satisfy it. -/
theorem actual_collision_empty_of_comparable_candidate_palettes
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ v, exponent v ≤ n)
    (honeLoss : ∀ v, (active C v).card ≤ n - exponent v + 1)
    (hcomparable :
      ∀ r ∈ forwardReverseBridgeSoftCarriers C exponent,
        retainedActive C r.1 ⊆ retainedActive C r.2 ∨
          retainedActive C r.2 ⊆ retainedActive C r.1) :
    actualForwardReverseCollisionWords C exponent hexp honeLoss = ∅ := by
  classical
  ext word
  constructor
  · intro hw
    have hi :=
      actual_collision_subset_incomparable_bridge_words
        C exponent hexp honeLoss hw
    obtain ⟨r, hr, _⟩ := Finset.mem_biUnion.mp hi
    have hdata := Finset.mem_filter.mp hr
    rcases hcomparable r hdata.1 with hsub | hsub
    · exact False.elim (hdata.2.1 hsub)
    · exact False.elim (hdata.2.2 hsub)
  · intro hw
    simpa using hw


/-- The filtered candidate pool also has EXACT DYADIC word mass,
without repeated overlap-face contributions. -/
theorem incomparable_bridge_soft_words_card_eq_dyadic_sum
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (incomparableBridgeSoftWords C exponent).card =
      ∑ r ∈ incomparableBridgeSoftCarriers C exponent,
        2 ^ (commonRetainedInactive C r.1 r.2).card := by
  classical
  have hpair :
      ((incomparableBridgeSoftCarriers C exponent : Finset (V × V)) :
        Set (V × V)).PairwiseDisjoint (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply overlapCarrierWords_pairwiseDisjoint C
    · have hp' : p ∈ incomparableBridgeSoftCarriers C exponent := by
        simpa using hp
      have hbridge := (Finset.mem_filter.mp hp').1
      have hsoft := (Finset.mem_filter.mp hbridge).1
      exact ((mem_softOverlapCarrierPairs C p).1 hsoft).1
    · have hq' : q ∈ incomparableBridgeSoftCarriers C exponent := by
        simpa using hq
      have hbridge := (Finset.mem_filter.mp hq').1
      have hsoft := (Finset.mem_filter.mp hbridge).1
      exact ((mem_softOverlapCarrierPairs C q).1 hsoft).1
    · exact hpq
  unfold incomparableBridgeSoftWords
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro p hp
  have hbridge :=
    (Finset.mem_filter.mp hp).1
  have hsoft : p ∈ softOverlapCarrierPairs C :=
    (Finset.mem_filter.mp hbridge).1
  have hcarrier : p ∈ overlapCarrierPairs C :=
    ((mem_softOverlapCarrierPairs C p).1 hsoft).1
  obtain ⟨word, hword⟩ :=
    ((mem_overlapCarrierPairs C p).1 hcarrier).2
  exact retainedCompletionWords_inter_card
    C (Finset.mem_inter.mp hword).1
      (Finset.mem_inter.mp hword).2

/-- The TWO net-unpaid movable hard sources can now be charged only
to genuinely used covered sinks plus actual-collision mass; using
the necessary active-palette obstruction, the latter is bounded by
the STRICTLY FILTERED oriented bridge dyadic mass. The unused
eligible covered sink reserve is retained on the left. -/
theorem net_mobile_mass_plus_unused_sink_le_incomparable_bridge_dyadic
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
      (∑ r ∈ incomparableBridgeSoftCarriers C exponent,
        2 ^ (commonRetainedInactive C r.1 r.2).card) := by
  have hmass :=
    net_mobile_source_plus_unused_eq_covered_plus_actual
      C exponent hexp honeLoss
  have hsubset :=
    net_actual_collision_card_le_incomparable_bridge_mass
      C exponent hexp honeLoss
  have hdyadic :=
    incomparable_bridge_soft_words_card_eq_dyadic_sum
      C exponent
  omega

#print axioms incomparable_bridge_soft_words_subset_candidate
#print axioms incomparable_bridge_soft_words_card_eq_dyadic_sum
#print axioms net_mobile_mass_plus_unused_sink_le_incomparable_bridge_dyadic
#print axioms actual_collision_subset_incomparable_bridge_words
#print axioms net_actual_collision_subset_incomparable_bridge_words
#print axioms net_actual_collision_card_le_incomparable_bridge_mass
#print axioms actual_collision_empty_of_comparable_candidate_palettes

end OrderedEdgeColoring
end JSP000404Research
