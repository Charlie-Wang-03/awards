import JSP000404Research.ResidualCarrierLevelFourWayClassification
import JSP000404Research.ResidualTransportableHardGlobalInjection
import Mathlib.Tactic

/-!
# Exhaustive word-owned partition of the hard net remainder

The earlier net-accounting interface uses the genuine Boolean set
  unpaidHardOverlapWords \ (ascendingRigidWords ∪ descendingRigidWords).
We now identify it as the exact disjoint union of *whole faces* of two
carrier families:
  - unreserved transportable hard carriers;
  - unreserved rigid hard carriers outside BOTH mixed-rigid classes.

This equality does not assume a Hall expansion or true Boolean holes.
The proof explicitly uses unique ordered residual overlap-word ownership;
without this uniqueness subtraction does not commute with a biUnion.

The residual transportable class may be injected into covered singleton
or soft-overlap words, NOT into Boolean holes. The terminal rigid class
is left as the genuine geometric obstruction.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- Canonical unpaid hard carrier set AFTER every whole-face and
mixed-rigid face reservation. -/
noncomputable def netUnpaidHardCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) :=
  (hardOverlapCarrierPairs C).filter (fun p =>
    p ∉ surplusPayableHardCarrierPairs C exponent ∧
    p ∉ ascendingUnpaidRigidCarriers C exponent ∧
    p ∉ descendingUnpaidRigidCarriers C exponent)

@[simp] theorem mem_netUnpaidHardCarrierPairs
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ netUnpaidHardCarrierPairs C exponent ↔
    p ∈ hardOverlapCarrierPairs C ∧
    p ∉ surplusPayableHardCarrierPairs C exponent ∧
    p ∉ ascendingUnpaidRigidCarriers C exponent ∧
    p ∉ descendingUnpaidRigidCarriers C exponent := by
  classical
  simp [netUnpaidHardCarrierPairs]

/-- Two ordered hard carriers cannot own one common Boolean word. -/
theorem hard_carrier_word_owner_unique
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    {p q : V × V} {word : Fin n → Bool}
    (hp : p ∈ hardOverlapCarrierPairs C)
    (hq : q ∈ hardOverlapCarrierPairs C)
    (hpword : word ∈ carrierOverlapWords C p)
    (hqword : word ∈ carrierOverlapWords C q) :
    p = q := by
  have hpord : p.1 < p.2 :=
    ((mem_residualCarrierPairs C p.1 p.2).1
      ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1 hp).1).1).1
  have hqord : q.1 < q.2 :=
    ((mem_residualCarrierPairs C q.1 q.2).1
      ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1 hq).1).1).1
  obtain ⟨hl,hr⟩ :=
    completion_word_unique_ordered_pair C hpord hqord
      (Finset.mem_inter.mp hpword).1
      (Finset.mem_inter.mp hpword).2
      (Finset.mem_inter.mp hqword).1
      (Finset.mem_inter.mp hqword).2
  exact Prod.ext hl hr

/-- Exact WHOLE-FACE reconstruction of the net hard Boolean-word
remainder. In particular, no face is partly removed. -/
theorem remainingUnpaidHard_eq_netCarriers_biUnion
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    remainingUnpaidHardAfterMixedRigidWords C exponent =
      (netUnpaidHardCarrierPairs C exponent).biUnion
        (carrierOverlapWords C) := by
  classical
  ext word
  constructor
  · intro hw
    have hdata := (Finset.mem_sdiff.mp hw)
    obtain ⟨p,hhard,hnotPaid,hpw⟩ :=
      unpaidHardWord_has_unpayable_hard_carrier
        C exponent hdata.1
    have hnotA : p ∉ ascendingUnpaidRigidCarriers C exponent := by
      intro hpA
      have hwordA : word ∈ ascendingUnpaidRigidWords C exponent :=
        Finset.mem_biUnion.mpr ⟨p,hpA,hpw⟩
      exact hdata.2 (Finset.mem_union.mpr (Or.inl hwordA))
    have hnotB : p ∉ descendingUnpaidRigidCarriers C exponent := by
      intro hpB
      have hwordB : word ∈ descendingUnpaidRigidWords C exponent :=
        Finset.mem_biUnion.mpr ⟨p,hpB,hpw⟩
      exact hdata.2 (Finset.mem_union.mpr (Or.inr hwordB))
    exact Finset.mem_biUnion.mpr
      ⟨p, (mem_netUnpaidHardCarrierPairs C exponent p).2
        ⟨hhard,hnotPaid,hnotA,hnotB⟩,hpw⟩
  · intro hw
    obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hw
    have h := (mem_netUnpaidHardCarrierPairs C exponent p).1 hp
    have hunpaid :=
      unpayable_hard_carrier_words_subset_unpaid
        C exponent h.1 h.2.1 hpw
    apply Finset.mem_sdiff.mpr
    refine ⟨hunpaid,?_⟩
    intro hAB
    rcases Finset.mem_union.mp hAB with hA | hB
    · obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp hA
      have hrig := ((mem_ascendingUnpaidRigidCarriers
        C exponent q).1 hq).1
      have hqhard : q ∈ hardOverlapCarrierPairs C :=
        ((mem_rigidHardOverlapCarrierPairs C q).1 hrig).1
      have hpq := hard_carrier_word_owner_unique
        C h.1 hqhard hpw hqw
      have hpA : p ∈ ascendingUnpaidRigidCarriers C exponent := by
        simpa [hpq] using hq
      exact h.2.2.1 hpA
    · obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp hB
      have hrig := ((mem_descendingUnpaidRigidCarriers
        C exponent q).1 hq).1
      have hqhard : q ∈ hardOverlapCarrierPairs C :=
        ((mem_rigidHardOverlapCarrierPairs C q).1 hrig).1
      have hpq := hard_carrier_word_owner_unique
        C h.1 hqhard hpw hqw
      have hpB : p ∈ descendingUnpaidRigidCarriers C exponent := by
        simpa [hpq] using hq
      exact h.2.2.2 hpB

/-- Those of the net-unpaid carriers which DO admit the safe
outward/inactive coordinate, chosen by the exact hard definition. -/
noncomputable def netTransportableHardCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) :=
  (netUnpaidHardCarrierPairs C exponent).filter
    (fun p => HasOutgoingHardTransport C p.1 p.2)

/-- Those of the net-unpaid carriers which have NO safe transport.
These are the only true terminal rigid hard-face carriers. -/
noncomputable def netRigidHardCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (V × V) :=
  (netUnpaidHardCarrierPairs C exponent).filter
    (fun p => ¬ HasOutgoingHardTransport C p.1 p.2)

@[simp] theorem mem_netTransportableHardCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ netTransportableHardCarriers C exponent ↔
      p ∈ netUnpaidHardCarrierPairs C exponent ∧
      HasOutgoingHardTransport C p.1 p.2 := by
  classical
  simp [netTransportableHardCarriers]

@[simp] theorem mem_netRigidHardCarriers
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) (p : V × V) :
    p ∈ netRigidHardCarriers C exponent ↔
      p ∈ netUnpaidHardCarrierPairs C exponent ∧
      ¬ HasOutgoingHardTransport C p.1 p.2 := by
  classical
  simp [netRigidHardCarriers]

noncomputable def netTransportableHardWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (netTransportableHardCarriers C exponent).biUnion
    (carrierOverlapWords C)

noncomputable def netRigidHardWords
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) : Finset (Fin n → Bool) :=
  (netRigidHardCarriers C exponent).biUnion
    (carrierOverlapWords C)

/-- Carrier-level transport/rigid classes partition the net
unpaid hard family WITHOUT invoking any projected budget. -/
theorem netHardCarriers_eq_transportable_union_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    netUnpaidHardCarrierPairs C exponent =
      netTransportableHardCarriers C exponent ∪
        netRigidHardCarriers C exponent := by
  classical
  ext p
  simp only [Finset.mem_union, mem_netTransportableHardCarriers,
    mem_netRigidHardCarriers]
  constructor
  · intro hp
    by_cases htr : HasOutgoingHardTransport C p.1 p.2
    · exact Or.inl ⟨hp,htr⟩
    · exact Or.inr ⟨hp,htr⟩
  · rintro (⟨hp,_⟩ | ⟨hp,_⟩) <;> exact hp

/-- Exact Boolean-word partition: the remaining hard mass has
a transportable part and a terminal rigid part. -/
theorem remainingUnpaidHard_eq_transportable_union_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    remainingUnpaidHardAfterMixedRigidWords C exponent =
      netTransportableHardWords C exponent ∪
        netRigidHardWords C exponent := by
  classical
  rw [remainingUnpaidHard_eq_netCarriers_biUnion,
    netHardCarriers_eq_transportable_union_rigid]
  ext word
  simp only [Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨p,hp | hp,hw⟩
    · exact Or.inl ⟨p,hp,hw⟩
    · exact Or.inr ⟨p,hp,hw⟩
  · rintro (⟨p,hp,hw⟩ | ⟨p,hp,hw⟩)
    · exact ⟨p,Or.inl hp,hw⟩
    · exact ⟨p,Or.inr hp,hw⟩

/-- The two net hard Boolean word types are disjoint, by unique
hard carrier ownership rather than by source-word cardinality. -/
theorem net_transportable_rigid_words_disjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    Disjoint (netTransportableHardWords C exponent)
      (netRigidHardWords C exponent) := by
  classical
  apply Finset.disjoint_left.mpr
  intro word hwT hwR
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hwT
  obtain ⟨q,hq,hqw⟩ := Finset.mem_biUnion.mp hwR
  have hp' := (mem_netTransportableHardCarriers C exponent p).1 hp
  have hq' := (mem_netRigidHardCarriers C exponent q).1 hq
  have hpq := hard_carrier_word_owner_unique
    C ((mem_netUnpaidHardCarrierPairs C exponent p).1 hp'.1).1
      ((mem_netUnpaidHardCarrierPairs C exponent q).1 hq'.1).1
      hpw hqw
  exact hq'.2 (by simpa [hpq] using hp'.2)

/-- Exact mass identity for the net Boolean hard remainder. -/
theorem remainingUnpaidHard_card_eq_transportable_add_rigid
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (remainingUnpaidHardAfterMixedRigidWords C exponent).card =
      (netTransportableHardWords C exponent).card +
        (netRigidHardWords C exponent).card := by
  rw [remainingUnpaidHard_eq_transportable_union_rigid]
  exact Finset.card_union_of_disjoint
    (net_transportable_rigid_words_disjoint C exponent)

/-- Exact terminal rigid target mass, needing only the endpoint
profile budgets for the selected carrier families. -/
theorem netRigidHardWords_card_eq_sum_upper_target
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hbudget :
      ∀ p ∈ netRigidHardCarriers C exponent,
        exponent p.1 ≤ projectedFree C p.1 ∧
        exponent p.2 ≤ projectedFree C p.2) :
    (netRigidHardWords C exponent).card =
      ∑ p ∈ netRigidHardCarriers C exponent,
        2 ^ exponent p.2 := by
  classical
  have hpair :
      ((netRigidHardCarriers C exponent : Finset (V × V)) :
        Set (V × V)).PairwiseDisjoint (carrierOverlapWords C) := by
    intro p hp q hq hpq
    apply carrierOverlapWords_pairwiseDisjoint C
    · have hpn := ((mem_netRigidHardCarriers C exponent p).1
        (by simpa using hp)).1
      exact ((mem_overlapCarrierPairs C p).1
        ((mem_hardOverlapCarrierPairs C p).1
          ((mem_netUnpaidHardCarrierPairs C exponent p).1 hpn).1).1).1
    · have hqn := ((mem_netRigidHardCarriers C exponent q).1
        (by simpa using hq)).1
      exact ((mem_overlapCarrierPairs C q).1
        ((mem_hardOverlapCarrierPairs C q).1
          ((mem_netUnpaidHardCarrierPairs C exponent q).1 hqn).1).1).1
    · exact hpq
  unfold netRigidHardWords
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro p hp
  have hpnet := (mem_netRigidHardCarriers C exponent p).1 hp
  have hpdata := (mem_netUnpaidHardCarrierPairs C exponent p).1 hpnet.1
  have hrig : p ∈ rigidHardOverlapCarrierPairs C :=
    (mem_rigidHardOverlapCarrierPairs C p).2 ⟨hpdata.1,hpnet.2⟩
  exact (terminal_rigid_carrier_mass_and_zero_surplus_without_word
    C exponent hrig hpdata.2.1 hpdata.2.2.1 hpdata.2.2.2
    (hbudget p hp).1 (hbudget p hp).2).1

/-- Every net-transportable hard word belongs to the EXISTING
unconditionally transportable domain; its canonical global flip
lands in covered singleton/soft words, not genuine Boolean holes. -/
theorem netTransportableHardWords_subset_transportable
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    netTransportableHardWords C exponent ⊆
      transportableHardOverlapCompletionWords C := by
  intro word hw
  obtain ⟨p,hp,hpw⟩ := Finset.mem_biUnion.mp hw
  have hpdata := (mem_netTransportableHardCarriers C exponent p).1 hp
  have hh := ((mem_netUnpaidHardCarrierPairs C exponent p).1 hpdata.1).1
  have htr := (mem_transportableHardOverlapCarrierPairs C p).2
    ⟨hh,hpdata.2⟩
  exact Finset.mem_biUnion.mpr ⟨p,htr,hpw⟩

/-- The net transportable part is globally bounded by distinct
SINGLETON/soft COVERED sinks. It is NOT paid by Boolean holes. -/
theorem netTransportableHardWords_card_le_singleton_add_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (netTransportableHardWords C exponent).card ≤
      (singletonCompletionWords C).card +
        (softOverlapCompletionWords C).card := by
  have hsub := Finset.card_le_card
    (netTransportableHardWords_subset_transportable C exponent)
  have hbound := transportable_hard_mass_le_singleton_add_soft C
  omega

#print axioms hard_carrier_word_owner_unique
#print axioms remainingUnpaidHard_eq_netCarriers_biUnion
#print axioms remainingUnpaidHard_eq_transportable_union_rigid
#print axioms remainingUnpaidHard_card_eq_transportable_add_rigid
#print axioms netRigidHardWords_card_eq_sum_upper_target
#print axioms netTransportableHardWords_card_le_singleton_add_soft

end OrderedEdgeColoring
end JSP000404Research
