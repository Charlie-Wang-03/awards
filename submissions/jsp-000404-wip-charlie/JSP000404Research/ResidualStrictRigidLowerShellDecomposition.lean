import JSP000404Research.ResidualStrictUnusedLowerSinkClassification
import Mathlib.Tactic

/-!
# Localize global strict-rigid lower slack into disjoint oriented shells

Let S be the terminal rigid carriers with strict target exponent descent.
Their globally disjoint lower completion cubes contain all strict-rigid
source faces. The unoccupied lower-word set is not only a finite
set-difference: it decomposes exactly into the lower-minus-upper
completion shell of EACH strict carrier.

Each local shell consists exclusively of singleton or soft-overlap
COVERED words; there is no direct Boolean hole or profile surplus.
This exposes the local geometric objects that a missing global payment
argument would have to use.
-/

namespace JSP000404Research
namespace OrderedEdgeColoring

/-- A word in the lower-but-not-upper cube of one strict rigid carrier
cannot be a reverse rigid source word from ANY other strict carrier. -/
theorem strict_rigid_lower_shell_subset_unused
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2 ⊆
      netStrictRigidUnusedLowerWords C exponent := by
  classical
  intro word hw
  have hwlow := (Finset.mem_sdiff.mp hw).1
  have hnotup := (Finset.mem_sdiff.mp hw).2
  change word ∈ netStrictRigidLowerCapacityWords C exponent \
    netStrictDescentRigidWords C exponent
  apply Finset.mem_sdiff.mpr
  constructor
  · change word ∈
      (netStrictDescentRigidCarriers C exponent).biUnion
        (fun p => retainedCompletionWords C p.1)
    exact Finset.mem_biUnion.mpr ⟨q, hq, hwlow⟩
  · intro hwrigid
    unfold netStrictDescentRigidWords at hwrigid
    obtain ⟨r, hr, hrword⟩ := Finset.mem_biUnion.mp hwrigid
    have hqNet :=
      ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
    have hrNet :=
      ((mem_netStrictDescentRigidCarriers C exponent r).1 hr).1
    have hqHard :=
      ((mem_netUnpaidHardCarrierPairs C exponent q).1
        ((mem_netRigidHardCarriers C exponent q).1 hqNet).1).1
    have hrHard :=
      ((mem_netUnpaidHardCarrierPairs C exponent r).1
        ((mem_netRigidHardCarriers C exponent r).1 hrNet).1).1
    have hqRes : q.1 < q.2 ∧ IsResidual C q.1 q.2 :=
      (mem_residualCarrierPairs C q.1 q.2).1
        ((mem_overlapCarrierPairs C q).1
          ((mem_hardOverlapCarrierPairs C q).1 hqHard).1).1
    have hrRes : r.1 < r.2 ∧ IsResidual C r.1 r.2 :=
      (mem_residualCarrierPairs C r.1 r.2).1
        ((mem_overlapCarrierPairs C r).1
          ((mem_hardOverlapCarrierPairs C r).1 hrHard).1).1
    have hrword' :
        word ∈ retainedCompletionWords C r.1 ∩
          retainedCompletionWords C r.2 := hrword
    have heqLower : q.1 = r.1 :=
      residual_lower_completion_word_unique C
        hqRes.1 hrRes.1 hqRes.2 hrRes.2
        hwlow (Finset.mem_inter.mp hrword').1
    have heq : q = r :=
      hard_carrier_shared_endpoint_implies_same_pair
        C hqHard hrHard (Or.inl heqLower)
    have hwup : word ∈ retainedCompletionWords C q.2 := by
      simpa only [← heq] using (Finset.mem_inter.mp hrword').2
    exact hnotup hwup

/-- Exact decomposition, at WORD level, of every unused strict lower
slot as a lower-minus-upper shell from a strict rigid carrier. -/
theorem unused_strict_lower_words_eq_union_shells
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    netStrictRigidUnusedLowerWords C exponent =
      (netStrictDescentRigidCarriers C exponent).biUnion
        (fun q => retainedCompletionWords C q.1 \
          retainedCompletionWords C q.2) := by
  classical
  ext word
  constructor
  · intro hw
    have hw' :
        word ∈ netStrictRigidLowerCapacityWords C exponent \
          netStrictDescentRigidWords C exponent := hw
    have hwlower := (Finset.mem_sdiff.mp hw').1
    change word ∈
      (netStrictDescentRigidCarriers C exponent).biUnion
        (fun q => retainedCompletionWords C q.1) at hwlower
    obtain ⟨q, hq, hqword⟩ := Finset.mem_biUnion.mp hwlower
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, Finset.mem_sdiff.mpr ⟨hqword, ?_⟩⟩
    intro hwup
    have hwrigid : word ∈ netStrictDescentRigidWords C exponent := by
      unfold netStrictDescentRigidWords
      apply Finset.mem_biUnion.mpr
      refine ⟨q, hq, ?_⟩
      change word ∈ retainedCompletionWords C q.1 ∩
        retainedCompletionWords C q.2
      exact Finset.mem_inter.mpr ⟨hqword, hwup⟩
    exact (Finset.mem_sdiff.mp hw').2 hwrigid
  · intro hw
    obtain ⟨q, hq, hqw⟩ := Finset.mem_biUnion.mp hw
    exact strict_rigid_lower_shell_subset_unused C exponent hq hqw

/-- Different strict rigid carriers have disjoint local lower-minus-
upper shells, because even their full lower cubes are disjoint. -/
theorem strict_rigid_lower_shells_pairwiseDisjoint
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    ((netStrictDescentRigidCarriers C exponent : Finset (V × V)) :
      Set (V × V)).PairwiseDisjoint
        (fun q => retainedCompletionWords C q.1 \
          retainedCompletionWords C q.2) := by
  classical
  intro q hq r hr hqr
  change Disjoint
    (retainedCompletionWords C q.1 \
      retainedCompletionWords C q.2)
    (retainedCompletionWords C r.1 \
      retainedCompletionWords C r.2)
  apply Finset.disjoint_left.mpr
  intro word hqw hrw
  have hd : Disjoint (retainedCompletionWords C q.1)
      (retainedCompletionWords C r.1) := by
    exact netStrictRigidLowerCubes_pairwiseDisjoint
      C exponent hq hr hqr
  exact (Finset.disjoint_left.mp hd)
    (Finset.mem_sdiff.mp hqw).1
    (Finset.mem_sdiff.mp hrw).1

/-- Exact local-shell counting formula for the unused strict
lower completion capacity, with no cross-carrier duplication. -/
theorem unused_strict_lower_words_card_eq_sum_shells
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ) :
    (netStrictRigidUnusedLowerWords C exponent).card =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        (retainedCompletionWords C q.1 \
          retainedCompletionWords C q.2).card := by
  classical
  rw [unused_strict_lower_words_eq_union_shells]
  exact Finset.card_biUnion
    (strict_rigid_lower_shells_pairwiseDisjoint C exponent)

/-- The individual strict descent shells consist ONLY of covered
singleton or soft overlap words, never global Boolean holes. -/
theorem strict_rigid_lower_shell_subset_singleton_soft
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2 ⊆
      singletonCompletionWords C ∪ softOverlapCompletionWords C := by
  exact (strict_rigid_lower_shell_subset_unused C exponent hq).trans
    (unused_strict_lower_words_subset_singleton_soft C exponent)

/-- On EACH strict rigid carrier, the lower-minus-upper Boolean
shell has precisely the difference of the two projected cube sizes. -/
theorem strict_rigid_lower_shell_card_eq_projected_gap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    (retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2).card =
      2 ^ projectedFree C q.1 - 2 ^ projectedFree C q.2 := by
  have hnet :=
    ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hrigid := (mem_netRigidHardCarriers C exponent q).1 hnet
  have hhard :=
    ((mem_netUnpaidHardCarrierPairs C exponent q).1 hrigid.1).1
  have hsame := ((mem_hardOverlapCarrierPairs C q).1 hhard).2
  have hsub :=
    hard_no_transport_upper_cube_subset_lower C hsame hrigid.2
  rw [Finset.card_sdiff_of_subset hsub]
  rw [retainedCompletionWords_card C q.1,
    retainedCompletionWords_card C q.2]
  simp only [projectedFree]

/-- The one-layer endpoint saturation theorem converts EACH local
strict-rigid shell's projected dimension gap into the corresponding
dyadic target exponent gap; no global subtraction is needed. -/
theorem strict_rigid_lower_shell_card_eq_target_gap
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1)
    {q : V × V}
    (hq : q ∈ netStrictDescentRigidCarriers C exponent) :
    (retainedCompletionWords C q.1 \
        retainedCompletionWords C q.2).card =
      2 ^ exponent q.1 - 2 ^ exponent q.2 := by
  have hnet :=
    ((mem_netStrictDescentRigidCarriers C exponent q).1 hq).1
  have hrigid := (mem_netRigidHardCarriers C exponent q).1 hnet
  have hdata := (mem_netUnpaidHardCarrierPairs C exponent q).1
    hrigid.1
  have hrig : q ∈ rigidHardOverlapCarrierPairs C :=
    (mem_rigidHardOverlapCarrierPairs C q).2
      ⟨hdata.1, hrigid.2⟩
  have hb :=
    netRigidHardCarriers_endpoint_budgets_of_oneLayer
      C exponent hexp honeLoss q hnet
  have hsat :=
    terminal_rigid_carrier_both_saturated_without_word
      C exponent hrig hdata.2.1 hdata.2.2.1 hdata.2.2.2
      hb.1 hb.2
  rw [strict_rigid_lower_shell_card_eq_projected_gap C exponent hq]
  rw [← hsat.1, ← hsat.2]

/-- Localized dyadic strict-descent capacity: the entire unused lower
pool is the sum of independently certified per-carrier shell gaps. -/
theorem unused_strict_lower_words_card_eq_sum_target_gaps
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (netStrictRigidUnusedLowerWords C exponent).card =
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        (2 ^ exponent q.1 - 2 ^ exponent q.2) := by
  rw [unused_strict_lower_words_card_eq_sum_shells]
  apply Finset.sum_congr rfl
  intro q hq
  exact strict_rigid_lower_shell_card_eq_target_gap
    C exponent hexp honeLoss hq

/-- Potential bridge-soft collisions are bounded by the SUM of
strict descent local shell capacities. Every slot counted on the
right is still covered and unavailable as a direct true-hole charge. -/
theorem bridge_soft_card_le_sum_local_strict_gaps
    {V : Type*} [LinearOrder V] [Fintype V] {n : ℕ}
    (C : OrderedEdgeColoring V (n + 1))
    (exponent : V → ℕ)
    (hexp : ∀ x, exponent x ≤ n)
    (honeLoss : ∀ x, (active C x).card ≤ n - exponent x + 1) :
    (forwardReverseBridgeSoftWords C exponent).card ≤
      ∑ q ∈ netStrictDescentRigidCarriers C exponent,
        (2 ^ exponent q.1 - 2 ^ exponent q.2) := by
  have h :=
    bridge_soft_card_le_unused_strict_lower_words C exponent
  rw [unused_strict_lower_words_card_eq_sum_target_gaps
    C exponent hexp honeLoss] at h
  exact h

#print axioms strict_rigid_lower_shell_subset_unused
#print axioms strict_rigid_lower_shell_card_eq_projected_gap
#print axioms strict_rigid_lower_shell_card_eq_target_gap
#print axioms unused_strict_lower_words_card_eq_sum_target_gaps
#print axioms bridge_soft_card_le_sum_local_strict_gaps
#print axioms unused_strict_lower_words_eq_union_shells
#print axioms strict_rigid_lower_shells_pairwiseDisjoint
#print axioms unused_strict_lower_words_card_eq_sum_shells
#print axioms strict_rigid_lower_shell_subset_singleton_soft

end OrderedEdgeColoring
end JSP000404Research
